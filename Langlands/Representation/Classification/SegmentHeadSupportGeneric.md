# Generic subquotient tools for the support of segment-head derivatives

This internal helper module is the first of six modules behind the proof of
`Langlands.Classification.SegmentHeadDerivativeSupportTruncation`
(module `SegmentHeadDerivativeSupportTruncationProof`). It contains only
general facts about actual smooth subquotients. It mentions no segment, head,
derivative or supercuspidal support. All declarations live in the namespace
`Langlands.Classification.SegmentHeadSupport`.

## Subquotient laws

`isSubquotient_trans` and `isSubquotient_refl` show that the relation
`SmoothRep.IsSubquotient` is transitive and reflexive. Both pass through the
published bridge `SmoothRep.isSubquotient_iff_representation` to the
representation-level relation `WeylBranchPieces.IsSubquotient`. That relation
is already transitive and reflexive.
`subsingleton_of_isSubquotient` shows that a subquotient of a representation
with a subsingleton carrier has a subsingleton carrier.
`nontrivial_of_isIrreducible` records that an irreducible smooth
representation has a nontrivial carrier, because its module over the monoid
algebra is simple.

## Short exact sequences

`isSubquotient_or_of_exact` is the following statement for representations of
an arbitrary group on complex vector spaces. Let `i : A → B` and `q : B → C`
be intertwiners with `range i = ker q`, and let `X` be an irreducible
subquotient of `B`. Then `X` is a subquotient of `A` or of `C`. Write the
subquotient as a subrepresentation `S ⊆ B` with a surjection `f : S → X`.

- If `f` vanishes on `S ∩ ker q`, then `f` descends to the image `q(S) ⊆ C`
  through the published `exists_descend`, and `X` is a subquotient of `C`.
- Otherwise some `u ∈ S ∩ ker q` has `f u ≠ 0`. Then `P = i⁻¹(S)` is a
  subrepresentation of `A`. The composite `P → S → X` is nonzero, because
  `u` lies in `range i`. By irreducibility of `X` it is surjective, so `X` is
  a subquotient of `A`.

Injectivity of `i` and surjectivity of `q` are not needed.
`smooth_isSubquotient_or_of_exact` is the same statement for actual smooth
representations and smooth intertwiners.

## Finite length

`PreservesShortExact Φ` is a proposition about a functor between smooth
categories. It says that `Φ` sends every short exact sequence of actual smooth
intertwiners, with injective first map, surjective second map and middle
exactness, to a sequence with the same three properties. It is a local
definition used only to state the following lemmas. It is not a statement
from the literature.

`PreservesShortExact.subsingleton` shows that such a functor preserves
subsingleton carriers. Apply it to the identity sequence `Z → Z → Z`. Its
middle exactness forces the image of `Z` to vanish.

`exists_irreducible_of_isSubquotient_map` is the key finite-length lemma. Let
`Φ` preserve short exact sequences, let `Z` have finite length, and let `X` be
an irreducible subquotient of `Φ Z`. Then there is an irreducible subquotient
`τ` of `Z` such that `X` is a subquotient of `Φ τ`. The proof takes a
composition series of `Z` (Mathlib's
`isFiniteLength_iff_exists_compositionSeries`). It moves the series to
subrepresentations through
`Subrepresentation.subrepresentationSubmoduleOrderIso`. Then it inducts along
the series. The bottom term is zero, so its image is subsingleton by the
previous lemma and cannot contain `X`. At a step `S_i ⋖ S_{i+1}`, apply `Φ` to
the short exact sequence `S_i → S_{i+1} → S_{i+1}/S_i`.
`smooth_isSubquotient_or_of_exact` then places `X` either in the image of
`S_i`, where the induction hypothesis applies, or in the image of the simple
factor `S_{i+1}/S_i`. That factor is irreducible by the published
`LengthCriterionProof.isIrreducible_quotientRep_iff`, and it is an actual
subquotient of `Z`. The top term is identified with `Z` by
`Submodule.topEquiv`.

## Provenance and inputs

All statements are internal generic lemmas for this proof. They are standard
consequences of exactness and Jordan–Hölder series in module categories. No
assertion from the original literature is transcribed.

Direct imports:

- `Langlands.Representation.Tensor.SmoothSubquotients`, for the bridge
  `SmoothRep.isSubquotient_iff_representation` and `SmoothRep.isSubquotient_iff_exists`.
- `Langlands.Representation.Exponents.WeylBranchPiecesSubquotient`, for the
  representation-level relation `WeylBranchPieces.IsSubquotient` and
  `exists_descend`.
- `Langlands.Representation.Induction.BinaryProduct`,
  `Langlands.Representation.Parabolic.InductionExactnessProof` and
  `Langlands.Representation.Shahidi.IntertwiningInduced`. These supply the
  binary product, the exactness of normalized induction and the binary tensor
  splitting that the next module uses. This module only needs their imports
  to be loaded.
- `Langlands.Representation.Filtration.LengthCriterionProof`, for
  `mem_bot_iff`, `lower` and `isIrreducible_quotientRep_iff`.
- Mathlib's `RingTheory.Flat.Basic` and
  `LinearAlgebra.TensorProduct.RightExactness`.

None of these modules proves a segment derivative formula, a Jacquet formula
of a segment representation, or any two-supercuspidal irreducibility or
structure result. The complete closure audit of the whole proof is in
`SegmentHeadDerivativeSupportTruncationProof.md`.

Author: Worker 890.
