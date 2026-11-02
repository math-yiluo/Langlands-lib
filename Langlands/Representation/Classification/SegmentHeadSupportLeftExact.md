# Exactness of the binary product in its second factor

This internal helper module is the second of six modules behind the proof of
`Langlands.Classification.SegmentHeadDerivativeSupportTruncation`. It shows
that, for a fixed smooth representation `L` of `GL_a(F)` with `a > 0`, the
functor `X ↦ L × X` preserves short exact sequences of actual smooth
intertwiners. Here `L × X` is the published binary normalized product
`T.binaryNormalizedProductFunctor a b` applied to the pair `(L, X)`. All
declarations live in the namespace `Langlands.Classification.SegmentHeadSupport`.

## Consequences of `PreservesShortExact`

`PreservesShortExact` is the local exactness predicate of
`SegmentHeadSupportGeneric`.

- `PreservesShortExact.map_injective`: such a functor sends an injective
  intertwiner `i : S → P` to an injective intertwiner. Apply the predicate to
  `S → P → P / i(S)`.
- `PreservesShortExact.map_surjective`: such a functor sends a surjective
  intertwiner `q : P → Q` to a surjective intertwiner. Apply the predicate to
  `ker q → P → Q`.

## Linear algebra

`pairSplit_externalMap` compares two published tensor constructions. The
external tensor `FiniteTensor.externalMap f` of a pair of linear maps
`f 0, f 1`, read through the published splitting `Shahidi.pairSplit` of a
tensor product indexed by `Fin 2`, is the binary map `f 0 ⊗ f 1`. Both sides
are linear, so it suffices to compare them on pure tensors.

`shortExact_of_lTensor` is a statement about complex vector spaces. Let
`i : S → P` be injective, let `q : P → Q` be surjective, and let
`range i = ker q`. Let `ti : A → B` and `tq : B → C` be linear maps that become
`M ⊗ i` and `M ⊗ q` after linear identifications of `A`, `B`, `C` with
`M ⊗ S`, `M ⊗ P`, `M ⊗ Q`. Then `ti` is injective, `tq` is surjective and
`range ti = ker tq`. The proof uses Mathlib's `lTensor_exact` for middle
exactness, `Module.Flat.lTensor_preserves_injective_linearMap` for injectivity
(every complex vector space is flat) and `LinearMap.lTensor_surjective`.

## The binary product

- `preservesShortExact_binaryPositive_sectR`: for `a, b > 0`, the functor
  `X ↦ T.binaryPositiveProductFunctor ha hb (L, X)` preserves short exact
  sequences. On the inducing data it is the external tensor of the fixed
  identity map of `L` with the given map. The previous two lemmas show that the
  inducing sequence is short exact. The published
  `Parabolic.normalizedInductionExactness` for the block shape
  `BlockShape.binary a b` (normalized parabolic induction is exact) then gives
  the claim.
- `preservesShortExact_binaryRightZero_sectR`: the same statement for the
  published rank-zero model `T.binaryRightZeroTensorFunctor hb` (`b = 0`). On
  carriers this functor is the tensor product with `L` up to `ULift`, so the
  claim is `shortExact_of_lTensor` with `ULift.moduleEquiv`.
- `preservesShortExact_binaryNormalized_sectR`: the statement for the binary
  normalized product in every second rank `b`. The published case equations
  `T.binaryNormalizedProductFunctor_of_right_eq_zero` and
  `T.binaryNormalizedProductFunctor_of_pos` reduce it to the two previous
  lemmas.

## Provenance and inputs

All statements are internal generic lemmas. The exactness of `L × -` is the
standard consequence of the exactness of normalized parabolic induction
(Bernstein–Zelevinsky 1977, Proposition 1.9(a)) and of the exactness of the
tensor product over a field. No new assertion from the literature is
transcribed.

Direct import: `Langlands.Representation.Classification.SegmentHeadSupportGeneric`.
The published declarations used come from its imports
`Langlands.Representation.Parabolic.InductionExactnessProof`
(`Parabolic.normalizedInductionExactness`),
`Langlands.Representation.Induction.BinaryProduct` (the binary product
functors and their case equations) and
`Langlands.Representation.Shahidi.IntertwiningInduced` (`Shahidi.pairSplit`
and `Shahidi.pairSplit_tprod`). The complete closure audit is in
`SegmentHeadDerivativeSupportTruncationProof.md`.

Author: Worker 890.
