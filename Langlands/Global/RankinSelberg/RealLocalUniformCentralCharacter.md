# Central scalar action on the real uniform Whittaker model

`RealJacquet.RealUniformWhittakerCentralCharacterStatement` asserts that, for
`realRank ds = r+1`, every `W` in the exact real uniform Whittaker coefficient
space satisfies

`W (g * scalar z) = (RealJacquet.determinant ds z : ℂ) * W g`

for every real unit `z`. `realUniformWhittakerCentralCharacter` proves this
without identifying the coefficient space with a continuous globalization.

On the positive scalars the proof uses the central Lie action supplied by
`realStandardLie_identity`. The intertwining relation transfers that action
to each coefficient. Applying the chain rule to the curve `g exp(t I)`
makes the coefficient satisfy the scalar differential equation with
coefficient `realStandardCentralExponent (r+1) ds`. The solution has
multiplier `exp(t * realStandardCentralExponent (r+1) ds)`. On a
positive scalar `exp(t)` this multiplier equals the product of the block
determinants: a rank-one character contributes its exponent, while the two
position exponents of an induced block sum to twice the inducing exponent,
and the sign and phase of that block are both trivial at positive scalars.
The proof verifies the product formula by induction on the block list.

At `-1` the proof transfers `standard_mul_minusOne` via the compact
intertwining relation. A negative scalar is the product of its positive
opposite with `-1`; the block determinant product has the corresponding sign
law. Finally a pointwise covariance relation is the kernel of a difference
of two linear evaluations on functions. That kernel contains every
intertwiner image, hence their supremum.

This is an internal coefficient-space lemma for additive-character
normalization. It uses only the supplied compact/Lie equations (as in the
scalar ODE argument of `ComplexLocalWhittakerChangeCharacter`), not stability
under arbitrary noncompact right translations. It gives no analytic
continuation or functional equation.
