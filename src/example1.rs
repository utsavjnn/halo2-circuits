use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    plonk::*, poly::Rotation, pasta::Fp, dev::MockProver
};

#[derive(Debug, Clone)]
struct ACell<F: FieldExt>(AssignedCell<F, F>);

// Defines the configuration of all the columns, and all of the column definitions
// Will be incrementally populated and passed around
#[derive(Debug, Clone)]
struct FiboConfig {
    pub advice: [Column<Advice>; 3],
    pub select: Selector,
}

struct FiboChip<F: FieldExt> {
    config: FiboConfig,
    _marker: PhantomData<F>, // no meaning here
    // In rust, when you have a struct that is generic over a type parameter (here F),
    // but the type parameter is not referenced in a field of the struct,
    // you have to use PhantomData to virtually reference the type parameter,
    // so that the compiler can track it.  Otherwise it would give an error. - Jason
}

impl<F: FieldExt> FiboChip<F> {
    // Default constructor
    fn construct(config: FiboConfig) -> Self {
        Self { config, _marker: PhantomData }
    }

    // Going to generate a circuit and define a custom gate here
    fn configure(meta: &mut ConstraintSystem<F>) -> FiboConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();

        // If you dont enable equality you cant do any permutation checks inside this column
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);

        meta.create_gate("add", |meta|{
            // local gate constraint
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            // return the constraints
            vec![s * (a+b-c)]
        });

        FiboConfig { 
            advice: [col_a, col_b, col_c],
            select: selector
        }
    }

    fn assign_first_row(&self, mut layouter: impl Layouter<F>, a: Option<F>, b: Option<F>) -> Result<(ACell<F>,ACell<F>,ACell<F>), Error>{
        layouter.assign_region(||"first row", 
    |mut region|{

            self.config.select.enable(&mut region, 0)?; // kind of region selector

            let a_cell = region.assign_advice(
                || "a",
                 self.config.advice[0], // column selector
                  0, 
                ||a.ok_or(Error::Synthesis)).map(ACell)?;

            let b_cell = region.assign_advice(
                || "b",
                    self.config.advice[1],
                    0, 
                ||b.ok_or(Error::Synthesis)).map(ACell)?;

            let c_val = a.and_then(|a| b.map(|b| a+b));

            let c_cell = region.assign_advice(||"c", 
            self.config.advice[2], 0, ||c_val.ok_or(Error::Synthesis)).map(ACell)?;


            Ok((a_cell, b_cell, c_cell))
        })
    }

    fn assign_row(&self, mut layouter: impl Layouter<F>, prev_b: &ACell<F>, prev_c: &ACell<F>) -> Result<ACell<F>, Error>{ // Only return the last cell
        layouter.assign_region(||"next row", |mut region| {
            self.config.select.enable(&mut region, 0)?;

            // copy the value from prev_b to this rows b and constrains them to be equal
            // ** -- PERMUTATION CHECK -- **
            prev_b.0.copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;
            prev_c.0.copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;

            let c_val = prev_b.0.value().and_then(|b| prev_c.0.value().map(|c| *b + *c));

            let c_cell = region.assign_advice(|| "c", 
            self.config.advice[2], 0, ||c_val.ok_or(Error::Synthesis)).map(ACell)?;

            Ok(c_cell)
        })
    }
}

#[derive(Default)]
struct FibonacciCircuit<F> {
    pub a: Option<F>,
    pub b: Option<F>
}

impl<F: FieldExt> Circuit<F> for FibonacciCircuit<F> {
    type Config = FiboConfig;

    type FloorPlanner = SimpleFloorPlanner;

    // Circuit without witnesses, called only during key generation
    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    // Has the arrangement of columns. Called only during keygen, and will just call chip config most of the time
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config { //just tells about local gate constraints
        FiboChip::configure(meta)
    }


    // Take the output of configure and floorplanner type to make the actual circuit
    // Called both at key generation time, and proving time with a specific witness
    // *** Will call all of the copy constraints ***
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = FiboChip::construct(config);
        
        let (_, mut prev_b, mut prev_c) = chip.assign_first_row(
            layouter.namespace(|| "first row"), self.a, self.b)?;
        
        // we have to prove f(9) = z
        for _ in 3..10 {
            // assign row
            let c_cell = chip.assign_row(layouter.namespace(||"next row"),
             &prev_b, &prev_c)?;
            
            prev_b = prev_c;
            prev_c = c_cell;
        }
        
        Ok(())
    }
}

fn main() {
    let k = 4;
    let a = Fp::from(1); // f(0) // curve that halo2 uses
    let b = Fp::from(1); // f(1)

    let out = Fp::from(55); //f(9)

    let circuit = FibonacciCircuit {
        a: Some(a),
        b: Some(b),
    };

    // istance is public inputs
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    prover.assert_satisfied();
}
