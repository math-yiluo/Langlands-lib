# Full-recognition idempotence as an equivalence of affinoid diagrams

Author: Worker 36.

This module constructs the inverse to `fullRecognitionIdempotenceFunctor`,
its unit and counit, and an actual equivalence of recognized inclusion
categories. Its natural isomorphism of presented-affinoid diagrams retains
every full bounded restriction and identifies the corresponding spectrum
maps over the fixed ambient space.

## Source and provenance

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Proposition 1.2.13(ii)–(iii), printed p.21 /
PDF p.18. Registered source `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original passage was read. No source-specific errata file was found in
the available project and Library locations.

Part (ii) constructs the extended atlas and its canonical bounded
restrictions; part (iii) flattens successive finite special coverings to
prove idempotence. The present categorical formulation is derived internal
infrastructure, rather than a verbatim formulation from the source. It
uses the finite-cover construction and actual algebra comparisons from
`FullRecognitionIdempotence`, their full restriction naturality from
`FullRecognitionNaturality`, and recognition of actual whole local
domains. The category equivalence and diagram isomorphism are constructed
from these results; neither is an input hypothesis.

## Categories and inverse functor

For an indexed affinoid atlas `a`, set `B = a.fullRecognitionAtlas`.
The earlier category has objects `a.saturatedAtlas.RecognizedSubset`,
which are the indices of `B`. The iterated category has objects
`B.saturatedAtlas.RecognizedSubset`. Both have literal inclusion arrows,
each carrying its constructed contravariant bounded restriction.
Write `F` for the previously constructed
`a.fullRecognitionIdempotenceFunctor`, from the iterated category to the
earlier one.

`fullRecognitionIterationIndex V` recognizes
`B.originalLocalDomain V`: the actual whole local-domain presentation of
the earlier chart `V`. This constructs an iterated index `G(V)`.
`fullRecognitionIterationIndex_locus` proves
`G(V).locus = V.locus`, by the recognition locus formula, the original
whole-domain locus formula, and `V.range_chart`.

`fullRecognitionIterationFunctor` constructs `G` on literal inclusions
using these identities. Its identity and composition laws hold by the
construction of the inclusion categories.

## Unit, counit and equivalence

`fullRecognitionIdempotenceUnitComponent W` constructs
`W ≅ G(F(W))` by the unchanged literal loci.
`fullRecognitionIdempotenceCounitComponent V` similarly constructs
`F(G(V)) ≅ V`. Both directions are actual recognized inclusions. Their
inverse laws, and the naturality of the corresponding
`fullRecognitionIdempotenceUnitIso` and
`fullRecognitionIdempotenceCounitIso`, follow from uniqueness of inclusion
arrows.

`fullRecognitionIdempotenceEquivalence` packages `F`, `G`, the unit and the
counit into the actual category equivalence. Its triangle law uses the
same inclusion uniqueness. This asserts an equivalence of these
inclusion categories; the algebra diagram comparison below records the
stronger algebra information separately.

## Presented-affinoid diagram comparison

For an iterated chart `W`, let
`e_W = a.fullRecognitionIdempotenceAlgebraEquiv W`, an actual bounded
algebra equivalence from `W.algebra` to `F(W).algebra`.
`fullRecognitionIdempotenceAffinoidIso W` gives the affinoid isomorphism
from `op F(W).algebra` to `op W.algebra`. Its hom is the opposite of
`e_W.toBoundedAlgHom`; its inverse is the opposite of the bounded inverse
map. The two inverse laws follow from `e_W.apply_symm_apply` and
`e_W.symm_apply_apply` on every algebra element.

`fullRecognitionIdempotenceAffinoidNatIso` constructs

```
F ⋙ RecognizedSubset.toAffinoidSpace a.saturatedAtlas
  ≅ RecognizedSubset.toAffinoidSpace B.saturatedAtlas.
```

Naturality is the opposite of the full bounded equation from
`fullRecognitionIdempotenceFunctor_naturality`. For every inclusion `f`,
that equation identifies `e_U.comp f.restriction` with
`(F.map f).restriction.comp e_V`. Thus the natural isomorphism identifies
the entire presented-affinoid diagrams, including the maps on nonreduced
algebras.

`fullRecognitionIdempotenceAffinoidNatIso_over_ambient` further proves
that the spectrum map induced by the hom component sends a point in
`F(W)` to the same ambient point through `W.chart`. Its proof applies the
already constructed exact chart formula for `e_W`.

## Scope

The field is complete, normed and ultrametric. Field, ambient-space and
original-index universes are independent. No global Hausdorffness,
nontrivial valuation, reducedness, nonzero algebra or nonempty cover
premise is added.

The result covers iteration of this specific full-recognition
construction. Arbitrary equivalent-net invariance, maximal-atlas
uniqueness, unrestricted analytic morphism comparison, etale and
quasi-etale sites and Harris specialization remain further obligations.
