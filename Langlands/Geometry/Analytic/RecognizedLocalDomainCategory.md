# Actual local-domain and recognized-chart category comparison

Author: Worker 36.

This module constructs an equivalence between actual local full-domain
presentations in the full recognition atlas and its recognized-chart
inclusion category. The equivalence preserves literal ambient subsets,
and its comparisons are actual bounded algebra equivalences, natural for
every entire inclusion restriction. A natural isomorphism identifies the
two complete diagrams of actual affinoid algebras.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Proposition 1.2.13(ii), printed p.21 / PDF p.18,
which equips nested recognized affinoid domains with canonical bounded
restrictions, and the contained affinoid domains and induced atlases after
Definition 1.3.1, printed p.23 / PDF p.20. Registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this construction. No source-specific
errata file was found in the available project and Library locations.

The comparison is a derived categorical consequence of the proved actual
local-domain closure and full represented-domain uniqueness. It is not
asserted as a separately numbered result in the source. The categories
retain actual affinoid algebras and their bounded maps, and the comparison
constructs rather than assumes the inverse functor and algebra
isomorphisms. It concerns domain inclusions, not the unrestricted category
of analytic-space morphisms.

`fullRecognitionAtlas_hasAllLocalDomains` instantiates the existing
closure interface using the literal family equality proved in
`RecognizedDomainClosure`. This is a theorem about the constructed atlas,
not an added closure hypothesis.

`fullRecognitionLocalDomainFunctor`, denoted `F`, sends a
`LocalDomain a.fullRecognitionAtlas` to the recognized chart constructed
from its actual original index and full domain. Its locus is literally
the original local-domain locus. Each actual inclusion supplies the
corresponding recognized inclusion on those same subsets. Identity and
composition are retained by construction.

`fullRecognitionWholeDomain` regards a recognized chart `V` as the
actual whole full domain in that original chart of the same atlas.
Its algebra is unchanged, its locus equals `V.locus`, and its ambient
map is exactly `V.chart`. `fullRecognitionWholeDomainFunctor`, denoted
`G`, sends a recognized inclusion to the constructed actual local-domain
inclusion between those whole presentations.

`fullRecognitionWholeDomainFunctor_map_restriction` proves that the
restriction stored by `G` is exactly the original recognized bounded
restriction. The proof uses the structural equation of the full
local-domain restriction and the theorem recovering the original atlas
restriction when one original chart lies in another. Since both domains
are whole, their base maps are identities. Thus the equality concerns all
algebra elements and retains nilpotent information; it is not deduced
from equality on spectra.

`fullRecognitionLocalDomainUnitIso` constructs the unit from the actual
local-domain isomorphism on equal literal loci. The local-domain category
stores actual bounded restrictions and their structural equations; its
proved thinness gives naturality of this isomorphism.
`fullRecognitionLocalDomainCounitComponent` and
`fullRecognitionLocalDomainCounitIso` construct the counit by literal
recognized inclusions in both directions, since the two round trips
have the same ambient locus. Their inverse identities and naturality
follow from uniqueness of recognized inclusions.
`fullRecognitionLocalDomainEquivalence` bundles these actual functors,
unit, counit and the proved triangle identity.

`fullRecognitionWholeDomainFunctor_toAffinoidSpace` identifies the
whole-domain functor followed by the actual affinoid-space realization
with the recognized category's own affinoid-space realization. Its object
equality keeps the original algebra unchanged; its arrow equality is
the entire restriction identity above.
`fullRecognitionLocalDomainAffinoidNatIso` then applies the actual
affinoid-space functor to the unit and uses that functor equality to
construct a natural isomorphism

```text
LocalDomain.toAffinoidSpace a.fullRecognitionAtlas ≅
  F ⋙ RecognizedSubset.toAffinoidSpace a.saturatedAtlas.
```

These are the existing opposite categories of actual presented affinoid
algebras, so this identifies their original bounded arrows as well as
their objects.

`fullRecognitionLocalDomainAlgebraEquiv U`, denoted `eᵤ`, extracts the
actual bounded algebra equivalence from the unit at `U`. It goes from
`U.algebra` to `(F.obj U).algebra`. For every actual inclusion
`f : U ⟶ V`, its naturality theorem proves the entire bounded equation

```text
eᵤ.toBoundedAlgHom.comp f.restriction =
  (F.map f).restriction.comp eᵥ.toBoundedAlgHom.
```

The proof applies the restriction field to inverse-unit naturality and
then uses the proved recovery of `G`'s full restrictions. These bounded
equivalences arise from actual local-domain isomorphisms; no comparison
is inferred from spectrum points.

`fullRecognitionLocalDomainAlgebraEquiv_chart` identifies the two ambient
maps through the spectrum homeomorphism of this same bounded equivalence:

```text
(F.obj U).chart x = U.ambientMap (eᵤ.spectrumHomeomorph x).
```

It uses the actual local inclusion's ambient naturality and the unchanged
whole-domain chart formula. The direction of the spectrum homeomorphism
is contravariant to the algebra equivalence.

The coefficient-field, ambient-space and original-index universes remain
independent. The complete ultrametric field may have trivial valuation.
No ambient Hausdorff, reducedness, nonzero-algebra or nonempty-cover
hypothesis is added. All imported domains and local inclusions retain
their full represented-domain universal properties.

This unit identifies the domain-inclusion categories and their actual
algebra diagrams. Equivalent-net invariance and idempotence of the full
recognition construction, maximal-atlas uniqueness and the unrestricted
analytic morphism-category identification remain separate. Analytic
étale and equivariant sites and the Harris tower specialization are
also outside this construction.
