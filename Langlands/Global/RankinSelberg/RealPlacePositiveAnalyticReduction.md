# Real-place reduction with the rank-one equal case proved

This internal module combines the real Tate proof and the global
rank-one equal-rank calculation with the convention, scalar-action, reflection
and parameter-determinant reductions. The real standard-module
nonvanishing proof supplies the remaining algebraic input through
`RealPlaceAnalyticReduction`.

`realEqualAtRank_zero` proves the existing `RealEqualAtRankStatement 0`
without a hypothesis: the real Tate theorem is supplied by
`Langlands.LocalFactor.RealTate.realArchimedeanTateStatement`.

The main conditional proposition,
`RealPlacePositiveAnalyticReductionStatement.{u}`, retains
`RealPositiveJacquetRestrictionEquationStatement.{u}`. This is the earlier
analytic restriction premise with the equal-rank index restricted to `r > 0`;
the unequal-rank part is unchanged. It still quantifies over the same actual
global Whittaker restrictions, characters, real places, parameters and
compatible quotient measures, and retains the same analytic and normalization
obligations. It preserves the field universe `u`.

The theorem `realPlacePositiveAnalyticReduction` proves the main implication.
It uses the known rank-one theorem when the equal-rank index is zero.
For unequal ranks and positive equal ranks it applies the same convention
conversion as `realPlaceJacquetConventionReduction`, now using the proved
compact-scalar, reflection and parameter-determinant comparisons.

This is an internal composition of the included proofs. The full functional
equation remains open in unequal ranks and positive equal ranks until the
retained analytic premise is proved.

The included real Tate proof supplies convergence, unique meromorphic
continuation, the real local functional equation and Gaussian normalization
in the Library's conventions. Its implementation uses zeta integrability and
holomorphy, a Tate identity with Schwartz Gaussians, analytic gluing and
meromorphic normal form. The separate rank-zero helpers identify arbitrary
compatible quotient measures with the corresponding Haar scale and identify
actual rank-one Whittaker restrictions and contragredient parameters with
the characters used by the local calculation. These are the proofs
implemented in their respective paired modules; the present adapter adds
only the rank split and convention conversion.

The new analytic premise retains every original unequal-rank datum and
every positive equal-rank datum: all global characters and restrictions,
contragredient realizations, four parameter lists, compatible quotient
measures, and Schwartz functions in equal ranks. It retains convergence,
holomorphy, meromorphic continuation, the negative-parameter
source-convention equations, local-model membership and normalization
identification. It neither assumes the rank-zero equation nor changes the
Library target.

A check compiles the full combined source
and inspects the entry proposition: no errors or warnings, `Prop` returned,
and the field universe `u` remains free.

An inspection of the unconditional rank-zero theorem `realEqualAtRank_zero` shows that it has free universe `u` and only the axioms `propext`, `Classical.choice` and `Quot.sound`.
