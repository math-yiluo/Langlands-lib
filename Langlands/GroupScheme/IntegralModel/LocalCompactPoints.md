# Compactness of the actual local-field integral-point image

This internal specialization takes an arbitrary-universe nonarchimedean local
field `F`, an actual affine group scheme `G/F`, and a supplied
`IntegralModel 𝒪[F] F G`. It uses the canonical valuation integer subring,
its actual inclusion into `F`, and the existing canonical evaluation topologies.
Both equal and mixed characteristic are included.

`localFieldIntegralPointContinuousHom` specializes the existing
`integralPointContinuousHom` to this inclusion. Its continuity premise is
`continuous_subtype_val`, since the canonical algebra map is definitionally the
subring inclusion. The evaluation lemma preserves the original
`M.integralPointMap`, including the supplied `M.genericIso`.

`isCompact_integralPoints_localField` applies the published
`isCompact_integralPoints` from `IntegralModel.CompactPoints`. Mathlib's
`NumberTheory.LocalField.Basic` supplies compactness of `𝒪[F]`; its subtype
topology is Hausdorff and makes it a topological ring. The conclusion is
compactness of the original image `M.integralPoints` in exactly
`rationalPointTopology F G.X`.

This module is derived from the existing integral-image continuity and
compactness proofs and Mathlib's local-field integer-ring instances. It uses no
additional external mathematical input. It does not require reductivity of
either fibre and proves no maximality, model smoothness, or comparison with a
building fixer.
