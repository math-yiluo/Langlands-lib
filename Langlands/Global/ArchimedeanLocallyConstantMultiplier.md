# Locally constant multiplication and genuine archimedean differentials

Author: Worker 2. This internal construction uses the existing
`ArchimedeanGL.SmoothFunctions` on completion-based infinite adelic matrices,
with real smoothness in the published mixed coordinates and complex
coefficients. The number field is in an arbitrary universe, and every
natural rank is allowed.

Multiplication by an actual locally constant complex-valued function is
complex-linear and preserves these smooth functions. Locally it agrees with
a constant scalar multiple; the existing smooth submodule and locality of
manifold smoothness prove membership.

The coordinate extension of the product agrees near every unit with the
constant scalar at that unit times the original coordinate extension.
Continuity of the inverse units chart and the coordinate homeomorphism
transfer local constancy to that neighborhood. Equality of local Fréchet
derivatives and the constant-scalar derivative formula prove commutation
with the actual real directional differential.

`complexSmoothLieAction_locallyConstantMultiplier` extends this commutation
to the published complexified Lie algebra by tensor induction: on a pure
tensor it is scalar multiplication of the real identity, and addition
preserves it. `envelopingAction_locallyConstantMultiplier` proves the
identity for every element of the actual universal enveloping algebra.
The proof chooses a preimage in the tensor algebra under the defining
quotient map and inducts on that tensor. Scalar elements commute,
Lie generators use the complex identity, and products and sums preserve
commutation. This follows the existing internal induction route in
`ArchimedeanEnvelopingLawsProof`, with the multiplier in place of left
translation.

The application and evaluation lemmas identify the actual output functions:
at every group point g, applying any enveloping differential to c times f
gives c(g) times that differential applied to f. Restricting along the
existing center inclusion gives `centerAction_locallyConstantMultiplier`.
The scalar function need not be nonzero, multiplicative, or of finite
order. The operator is an algebraic complex-linear endomorphism;
no topology on the smooth-function carrier or continuity of the operator
is asserted here.

This is a derived internal construction from the published genuine
archimedean differential and pinned Mathlib local calculus. No new
comparison with original literature or full automorphic preservation is
claimed. In particular, this module supplies no determinant-character
specialization, finite-adelic gluing, growth condition, or total twist
of an automorphic operator realization.
