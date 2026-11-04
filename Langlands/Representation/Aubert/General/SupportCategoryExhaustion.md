# Passage from finitely generated to arbitrary smooth support objects

This internal reduction by Worker 288 applies to an endofunctor of the actual
smooth complex representation category. It retains independent group and
carrier universes and the full all-irreducible-subquotient definition of
`IsInSupportCategory`.

`finiteSpanFunctorImage F E s` is the actual invariant range of `F` applied to
the inclusion of the group-algebra span of the finite vector set `s`.
`finiteSpanSubtype_range_directed` and `finiteSpanSubtype_range_cover` verify
that these inclusions have directed ranges and cover every vector of `E`.
Directedness follows from `finiteSpanSubrepresentation_directed`; a vector
lies in the range from its singleton span.

`inductionJacquet_iSup_finiteSpanFunctorImage` proves exhaustive invariant sum
for the actual normalized `inductionJacquetFunctor`. Its explicit hypotheses
are compactness of the left quotient by the chosen parabolic and
`Jacquet.Localization.IsLimitOfCompactSubgroups` for the chosen unipotent
subgroup. The proof supplies the actual span inclusions to
`inductionJacquetFunctor_exists_preimage_of_directed_cover`, with their
injectivity from `SmoothRep.subtype_injective`, directedness and vectorwise
cover. That theorem places each output vector in one image, hence in their
supremum.

`isInSupportCategory_of_iSup_ranges` assumes that a family of actual
intertwiners into `B` has invariant ranges whose sum is the whole of `B`. If
every source belongs to the support category, then `B` belongs to it. Each
invariant image is an actual quotient of its source, by
`SmoothRep.image_isQuotient`. Subquotient closure gives support of these images.
`IsInSupportCategory.iSup` gives support of their invariant sum, and the
surjective inclusion of the full subrepresentation transfers this to `B`.
The image family may have any indexing universe and may be empty.

`supportCategory_preserved_of_finiteGeneration` has two explicit inputs:

- Every `F.obj E` is the invariant sum of the ranges of the maps obtained by
  applying `F` to the inclusions of the finite invariant spans of `E`.
- `F` preserves the specified support category on every representation that is
  finitely generated over the group algebra.

The proof applies the first lemma to those ranges. Each finite invariant span
is supported because it is an actual subrepresentation of `E`. Its finite
generation is `SmoothRep.finiteSpanSubrepresentation_finite`, so the second
input proves support of its image under `F`.

`supportCategory_inductionJacquet_of_finiteGeneration` applies this reduction
to the actual normalized induction-Jacquet functor, using its proved
finite-span image exhaustion. It keeps compact quotient, compact-limit
unipotent part and support preservation on every finitely generated input as
explicit hypotheses.

This establishes the passage to arbitrary smooth objects once those two
inputs have been proved for an endofunctor. For actual normalized
induction-Jacquet, exhaustion is proved with the displayed topological
inputs, while stage support preservation remains a premise. This does not prove
`RationalSupportCategoryInductionJacquetStatement`. In particular, a finitely
generated smooth representation need not have finite length; this reduction
does not replace the finitely generated input obligation by an irreducible
input claim.

The provenance is internal and derived from invariant spans, actual directed
functor images, invariant-sum closure and subquotient closure. The directed-cover
theorem uses `Induction.exists_finset_doubleCoset_cover` for induction, actual
localization quotient representatives, and
`Jacquet.Localization.map_injective_of_smooth` for Jacquet injectivity.
No classification, character independence, geometric lemma or adjointness
declaration is invoked by these proof bodies. The imported
invariant-sum algebra reaches the general subquotient algebra through the
Library's classification module; no GL-specific support result is used.
