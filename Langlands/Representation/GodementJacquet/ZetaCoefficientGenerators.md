# Smooth coefficient generators for the actual matrix value module

This internal module closes a linear-span step in the analytic induction
argument. The published matrix rational-value family allows every function in
the complex span of the actual bi-smooth coefficients. A local-section
realization argument can instead start with a single smooth functional and a
single smooth vector in each block. The results here justify that reduction at
the level of the full Laurent value modules.

`matrixGeneratorRationalValues` is the set of actual shifted rational values
for those individual coefficients, over every full-matrix Schwartz test. It
uses `HasShiftedRationalValue`, including actual convergence on a right
half-plane and the guarded rational-continuation relation. It is contained in
the published matrix value set because each individual coefficient belongs to
the defining complex span.

`zetaSpan_matrixRationalValues_eq_generatorSpan` assumes `q > 1` and existence
of an actual rational value for every individual smooth coefficient and test.
It proves equality of the two Laurent spans. For the forward inclusion, the
linear-closure theorem from `ZetaLinear` extends values in the generator
Laurent span to every coefficient in the complex span. Uniqueness of rational
continuation identifies any given published value with the value so obtained.
The other inclusion follows directly from containment of the value sets.
Neither this reasoning nor the uniqueness step discards the denominator
nonvanishing conditions. The full matrix analytic predicate supplies the
required rationality premise, as recorded in its specialization.

`zetaSpan_matrixRationalValues_mul_le_of_generator_products` applies this
equality separately to two blocks, with independent ranks and carrier
universes. The product of the two Laurent spans is the Laurent span of all
products of their generator values, by `ProductGenerators`. Thus membership of
every such product in a fixed Laurent submodule implies containment of the
product of the full published value modules. The premise retains every pair
of tests, smooth functionals, smooth vectors and their actual rational values.
It can be used after an actual induced-integral realization establishes those
memberships.

The provenance is derived linear algebra: the published coefficient-span and
rational-value definitions, linear closure and continuation uniqueness in
`ZetaLinear`, and the algebraic product-span identity in `ProductGenerators`.
No smoothness or admissibility of the whole representation is needed. This
module does not construct a local section, compute a noncompact integral, or
prove analytic induction or reverse generation for an induced representation.
