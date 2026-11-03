# Universe-general evaluation on actual affine points

This internal extension of `PointManifold.RegularEvaluation` permits an arbitrary
coefficient universe: `k : Type u` with `RCLike k`. The affine object is over
`Spec k` in that universe. The source normed space, model space and parameter
space have three independent universes. The actual `PointTopology.RingPoint`
carrier and its established evaluation topology are used throughout.

`regularEvaluation` is the algebra map of `affineSchemePointEquiv`.
`regularEvaluation_eq_pullback` identifies its ring map with the point's actual
global-section pullback followed by `Γ(Spec k) ≅ k`; its proof uses faithfulness
of `Spec` and naturality of the affine spectrum isomorphism. The continuity
lemmas characterize the existing topology by precisely these values.
`regularEvaluation_postcomp` identifies values after an actual relative
morphism with coordinate-ring pullback.

`RegularSmooth I f` asks that every regular-function value on the parameter
family is real `C∞`. Constants and postcomposition preserve it. This definition
assigns no manifold to the target. The source needs a charted-space structure,
but no `IsManifold` hypothesis is needed for these tests or the preservation
lemmas. `regularEvaluation_typeZero` and `regularSmooth_typeZero_iff` identify
these definitions exactly with the published Type 0 ones, for the same actual
points and functions.

Worker 94 adapted Worker 274's published `RegularEvaluation` definitions and
proofs by making the coefficient universe explicit, and added the exact Type 0
comparisons. The provenance is internal, through the published affine-point
comparison and Mathlib's manifold calculus. Existence of charts from algebraic
smoothness remains a separate obligation.
