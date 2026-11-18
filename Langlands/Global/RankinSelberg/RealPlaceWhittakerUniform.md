# Uniform growth of all derivatives of actual real-place Whittaker restrictions

This internal supporting result proves `RealPlaceWhittakerUniformGrowthStatement.{u}`.
For an actual cuspidal realization `T` of `GL_(r+1)` over a number field `F` with compact
adele quotient, fix a real place `w` and a finite adelic component `b`. There is a natural
exponent `N` such that, for every standard adelic additive character `χ`, every vector
`x` of `T`, and every finite list `Xs` of real matrix directions, there is a nonnegative
constant `C` satisfying

`‖R(Xs) W_x(g)‖ ≤ C * realMatrixHeight(g)^N`

for every `g ∈ GL_(r+1)(ℝ)`. Here `W_x(g)` is the actual global Whittaker function of `x`
evaluated at `realPlacePoint F (r+1) w g * finitePoint F (r+1) b`. The exponent is chosen
before the character, vector, and entire derivative word. The constant may depend on
all three. The statement retains the free number-field universe.

`iteratedLieAction T w Xs x` uses the genuine Lie action
`T.realization.realPlaceLieAction w (1 ⊗ X)` on `T.Space`. It is a right fold: on `X :: Xs`,
the action in direction `X` acts after all actions in `Xs`. The function derivative
`RealLocalWhittaker.iteratedRightDerivative` uses the same order, and the empty word is
the identity on vectors and functions.

The proof of `iteratedRightDerivative_eq_restriction` is list induction. For a nonempty
word, the induction hypothesis identifies the tail derivative with the restriction of a
derived vector of the same realization. The unconditional smoothness theorem for every
actual restriction applies to that vector. The previously proved
`rightDerivative_eq_restriction` then identifies the outer function derivative with its
genuine Lie action. Consequently every derivative word is itself an actual restriction
of a vector in `T`; `contMDiff_iteratedRightDerivative` also proves its smoothness.

`exists_uniform_norm_cuspWhittaker_realPlace_le` supplies one polynomial exponent for all
vectors and standard characters of this fixed realization and slice. Apply its bound to
`iteratedLieAction T w Xs x` and rewrite with the comparison just proved. This gives
`exists_uniform_norm_iteratedRightDerivative_le`; the entry theorem packages it as the
displayed proposition.

Provenance is internal. The result composes the genuine Whittaker derivative comparison,
the proved actual restriction smoothness, and the common-exponent global determinant
bound from `ArchimedeanWhittakerRegularity`, specialized through the real determinant and
height estimate in `RealPlaceWhittakerAnalyticProof`.

The scope is actual global restrictions. No uniform exponent for arbitrary elements of
the internal local coefficient space is claimed. This supporting growth theorem proves
no local convergence, continuation, or functional equation; the full real-place
functional equation remains open.
