# The unequal-rank JPSS functional equation over every nonarchimedean local field

Module `Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationProof`.

`Langlands.RankinSelberg.localFieldUnequalRankFunctionalEquation` proves the published
`Langlands.RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement` at independent
universes `uF`, `uV`, `uW`. This is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), Theorem (2.7)(iii),
printed pages 390–391, for unequal ranks `r + 1 > n + 1`. By section (0.3), printed
page 375, it holds over every nonarchimedean local field, of any characteristic.

## Proof

The proof is one application of
`Langlands.AllField.RankinSelberg.localFieldUnequalRankFunctionalEquation_of_allField`
(module `LocalFieldUnequalRankFunctionalEquationReduction`). That reduction turns the
ported statement for the ambient data `LocalFieldData.ofInstances F` into the target with
its hypothesized residue cardinality, absolute value, uniformizer and Borel structures.
The ported statement is supplied by
`Langlands.AllField.RankinSelberg.unequalRankFunctionalEquation F (LocalFieldData.ofInstances F) n r`,
the all-field port of the Library's p-adic `Langlands.RankinSelberg.unequalRankFunctionalEquation`.
The port's Markdown describes how it combines the common gcd generator, the block-zero
gamma factor and its propagation to every complementary block.
