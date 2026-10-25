# Covariance of the actual enveloping and center differential actions

Author: Worker 459. Module: `Langlands.Global.ArchimedeanCovarianceProof`.
Namespace: `Langlands.Global.ArchimedeanGL`.

This proof targets the published
`EnvelopingCenterRightCovarianceStatement K n`, preserving its ordered
conjunction. All results allow an arbitrary universe, every number field
`(K : Type u) [Field K] [NumberField K]`, and every `n : ℕ`, including zero.
The group element ranges over the whole `InfiniteAdelicGL K n`.

Write `R(g)` for positive right translation `smoothRightAction K n g`,
`D(a)` for `envelopingAction K n a`, and `Ad(g)` for the appropriate
published conjugation map. The actual actions and algebraic objects are
imported unchanged. No covariance hypothesis or action certificate is supplied.

## Complex Lie covariance

`smoothRightAction_complexSmoothLieAction` proves
`R(g) (complexSmoothLieAction X f) =
  complexSmoothLieAction (complexLieConjugation g X) (R(g) f)`.
Tensor induction on the whole complexified Lie algebra reduces the proof to
pure tensors and sums. For `z ⊗ X`, the published pure-tensor formulas for the
Lie action and conjugation reduce the identity, by complex linearity of
`R(g)`, to `z` times
`smoothRightAction_smoothDifferential_realLieConjugation`.
That theorem is imported from the published
`Langlands.Automorphic.RealDifferentialCovarianceProof`; this module does not
repeat its analytic chain-rule argument. Additivity proves the sum case.

## Enveloping covariance

`envelopingRightCovariance` has exactly the type
`EnvelopingRightCovarianceStatement K n`. It proves
`R(g) (D(a) f) = D(envelopingConjugation g a) (R(g) f)`.

The universal enveloping algebra is the existing quotient of the tensor
algebra. Quotient induction reduces the result to the image of a tensor-algebra
element under `UniversalEnvelopingAlgebra.mkAlgHom`. Mathlib's
`TensorAlgebra.induction` then reduces to scalars, canonical Lie generators,
products and sums. Scalars act by scalar multiplication, so their case follows
from complex linearity. The generator formulas for `envelopingAction` and
`envelopingConjugation` reduce the generator case to the complex Lie covariance
above. For a product, multiplicativity of the quotient map, action and
conjugation gives `D(ab)f = D(a)(D(b)f)`; the two induction hypotheses apply
successively, with the hypothesis for `a` used at `D(b)f`.
Additivity proves the sum case. No assertion about injectivity of the canonical
Lie map or a choice of a basis is required.

## Center restriction and final theorem

`centerRightCovariance` has exactly the type `CenterRightCovarianceStatement K n`.
Apply enveloping covariance to `centerInclusion K n z`, then rewrite
`centerAction_apply` and `centerInclusion_centerConjugation`. This proves
covariance with `centerConjugation g z`; it asserts no pointwise fixation of
the center.

`envelopingCenterRightCovariance` pairs the two component proofs in the
published order and has exactly the type
`EnvelopingCenterRightCovarianceStatement K n`. The closing unapplied example
checks the complete parameter telescope. No positive-rank, compactness,
automorphy, growth or finiteness assumption occurs.

## Derived provenance

These are internal derived compatibility results from the published real
covariance theorem, actual complex Lie and enveloping actions, and actual
adjoint automorphisms. Mathlib supplies tensor and quotient induction.
The source framework and motivation are documented in the unchanged paired
Markdown of `Langlands.Global.ArchimedeanCovarianceStatement`; this proof
claims no new verbatim assertion from the original literature.
