# The concrete Cartan matrix frame and quadratic differential symbol

This internal construction combines the concrete normalized Cartan basis
from `ArchimedeanCasimirCartan` with the genuine differentiation and
enveloping action from `ArchimedeanSmoothDifferential` and
`ArchimedeanEnvelopingAction`. Its scope is the original archimedean real
matrix space over every number field and at every natural rank, including
zero. Worker 94 supplied the development; Worker 116 inspected it and
added the complete-parameter checks.

`leftMatrixFrame` maps a real matrix Lie direction `X` to `g * X` in the
original ambient real matrix space at an actual unit `g`. Multiplication
by the inverse unit supplies the inverse. The unit identities,
associativity and real linearity prove that this is a real linear
equivalence. `leftCartanMatrixBasis` transports the complete normalized
Cartan basis through this equivalence. All actual real matrix directions,
including both real directions at complex infinite places, are retained.
The carrier, norm and topology are the published ones.

`cartanCovectorForm` is a real quadratic form on the real algebraic dual
of this same matrix space. It is the finite sum of the square quadratic
map composed with evaluation at each left-frame basis vector.
`cartanCovectorForm_apply` gives the exact sum of real squares.
Nonnegativity follows term by term. If the sum vanishes, every square
vanishes, so the covector vanishes on the entire transported basis;
basis extensionality makes it zero. Conversely, the zero covector gives
zero. Nonnegativity and this zero criterion imply positivity on every
nonzero covector. These arguments also cover an empty basis: in that
case the dual is zero, and there is no nonzero covector. No new norm or
inner-product instance is introduced.

`smoothDifferential_iterated_apply` calculates two genuine left matrix
derivatives. For an actual group point `x`, write `g` for its matrix-unit
coordinates, `F` for `coordinateExtension f`, and `X`, `Y` for the two
underlying real matrices. The ambient function
`h ↦ fderiv ℝ F h (h * Y)` agrees on all units with the first directional
derivative. The published extension-independence lemma therefore
computes the second directional derivative from this function. Smoothness
of `F` near units makes its first derivative differentiable there.
The continuous-linear-map evaluation rule and the derivative of right
multiplication give exactly

`D²F(g)(g * X)(g * Y) + DF(g)(g * (X * Y))`.

The imported `envelopingAction_real_generator` identifies the actual real
generator with the published genuine differential operator.
`envelopingAction_cartanSquareSum` uses preservation of finite sums and
products by the genuine enveloping action. The pointwise theorem
`envelopingAction_cartanSquareSum_apply` then substitutes the iterated
formula term by term. It displays the entire second-order coefficient
and the first-order correction for the actual full square sum.

`cartanSecondOrderCoefficient` evaluates the finite second-order
coefficient on a real bilinear map. For a real covector, the bilinear
map `(v,w) ↦ ℓ(v) * ℓ(w)` is built from real multiplication and the
covector. `cartanCovectorForm_eq_secondOrderCoefficient` proves that
its coefficient evaluation is exactly `cartanCovectorForm`. This
describes the real coefficient convention; no convention inserting a
factor of `i` is asserted.

This construction is internal, derived from the imported actual Cartan
basis, unit multiplication, genuine enveloping action and Frechet product
rule. It assumes no principal-symbol certificate or differential-action
certificate. All declarations retain arbitrary number-field universe
and natural rank. It supplies concrete positive second-order coefficient
data. Analytic elliptic regularity, analyticity of solutions, polynomial
annihilation, admissibility, reproduction and automorphic derivative
growth remain separate obligations.
