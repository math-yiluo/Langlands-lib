# Atlas geometry over a monomorphism to a scheme

Author: Worker 1150.

This is a derived helper for the proof of
`MonomorphismLocallyFiniteTypeSchemeStatement`. It implements the kernel-pair
step of Stacks Project Lemma 67.27.10, Tag 0463, registered as
`stacks-mono-lft-schemehood-2026-11-02`. The proof uses the open diagonal
criterion for formal unramifiedness rather than the source's direct analysis of
fibres. The universe `u` is arbitrary.

Let `S` be a scheme, `F` an arbitrary presheaf on schemes over `S`, `W` and `Y`
schemes over `S`, `a : h_W ⟶ F` an etale transformation, and `f : F ⟶ h_Y` a
monomorphism. Suppose `a ≫ f` is the transformation induced by a scheme
morphism `w : W ⟶ Y`.

`atlasKernelPair_isPullback_of_mono` shows that any actual scheme pullback of
`w` with itself also represents the pullback of `a` with itself. The lifted
Yoneda functor preserves the scheme pullback. The resulting square for
`a ≫ f` is a pullback square for `a`, because the common postcomposition `f`
is a monomorphism; Mathlib's `PullbackCone.isLimitOfFactors` supplies precisely
this cancellation.

`atlasCompositeKernelPair` equips the actual scheme pullback
`W.left ×_[Y.left] W.left` with its structure over `S`.
`etale_kernelPair_snd_of_mono` uses this object. Its two projections
satisfy the preceding pullback statement. The definition of `IsEtale a` then
makes the second projection etale.

`formallyUnramified_of_etale_mono_composite` uses that the diagonal of
`w.left` is a section of this etale second projection. A section of an etale
scheme morphism is an open immersion, as follows from the open diagonal of
etale morphisms and Mathlib's postcomposition property. Mathlib's open
diagonal criterion therefore makes `w.left` formally unramified.

`locallyQuasiFinite_of_etale_mono_composite` additionally assumes
`LocallyOfFiniteType w.left`. The published theorem
`Langlands.AlgebraicGeometry.GenericFiniteness.locallyQuasiFinite_of_formallyUnramified`
then yields `LocallyQuasiFinite w.left`.

No sheaf or algebraic-space hypothesis on `F`, and no surjectivity hypothesis
on `a`, is required by these helpers. The last theorem requires local finite
type; the first three do not. These results prove atlas geometry only and do
not assert that `F` is represented by a scheme.
