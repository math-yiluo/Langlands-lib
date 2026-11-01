# Full strong-map restriction to actual source and target domains

Author: Worker 36.

This module constructs simultaneous restriction of a full strong map to
original-chart domains S and T. The explicit chartwise hypothesis requires
every original source chart contained in S to map into an original target
chart contained in T. It constructs the subspace map, retains every
original admissible bounded pullback, proves source restriction naturality,
and preserves strong quasi-isomorphisms when the ambient map carries S
exactly onto T. Nested domains receive their full strong inclusion from
the ambient identity.

The original source conventions are Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Definition 1.2.3 and Remark
1.2.4(i), printed p.16 / PDF p.13; Definitions 1.2.7 and 1.2.9,
printed pp.18–19 / PDF pp.15–16; and Definition 1.3.1, printed p.23 /
PDF p.20. Registered source: `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this unit. The extracted header of
PDF p.15 misreads the printed page number; the previously inspected
rendering identifies printed p.18. No source-specific errata file was
found in the project and Library locations.

The construction is derived infrastructure for the existing
fixed-original-chart presentations. It uses the published
`OriginalDomainStrongPresheaf`, `StrongAtlasQuasiIsomorphisms`, and
their actual subspace atlas and full strong-map dependencies. It is not
a proof of the unrestricted analytic-domain inverse-image assertion
of Definition 1.3.1.

The coefficient field is complete and ultrametric. Its universe u and
the point and chart universes v,w are independent; as in the imported
full strong-map definition, both ambient presentations use that same
triple. No directedness, greatest chart, nonempty-spectrum, reducedness,
or strictness assumption is added.

`StrongHom.MapsOriginalDomainCharts` is a proposition about the ambient
map and the actual contained source and target charts.
`MapsOriginalDomainCharts.mapsTo` uses the source domain's constructed
net, which covers all its actual points. Combining that point coverage
with the chart witnesses derives actual image containment in T; an
output map is not supplied independently. The lemmas `mono_source` and
`mono_target` retain its witnesses after shrinking the source domain or
enlarging the target domain.

`restrictDomainsBaseMap` restricts the continuous ambient map to the two
actual subspaces. `restrictDomainsBaseMap_admissible_iff` proves that
subspace admissibility at source chart c and target chart d is exactly
ambient admissibility at c.val and d.val. The constructed `restrictDomains`
therefore uses the original bounded pullback on every such pair. Its
chart formula and two-variable bounded compatibility are inherited from
the ambient map. `restrictDomains_apply_val` and `restrictDomains_pullback`
expose its actual point and entire bounded-map formulas.
`restrictDomains_restrictOriginalDomain` proves that direct source
restriction commutes on the complete maps by the same formulas.

`restrictDomains_chartImageLocus` proves that the target-chart spectrum
image locus is unchanged in the ambient coordinates. If the ambient
map is a strong quasi-isomorphism and its actual image of S equals T,
the ambient homeomorphism restricts to a homeomorphism S→T, and every
full affinoid-domain representation assertion is the corresponding
ambient assertion. This proves `IsQuasiIso.restrictDomains`. Its image
equality and chartwise witnesses are both explicit hypotheses; neither
an output inverse map nor a domain algebra is supplied as additional data.

The ambient identity satisfies the chartwise condition for S≤T by
retaining each contained original chart, giving `mapsOriginalDomainCharts_id`.
Its restriction `originalDomainStrongMap` is the full strong domain
inclusion. `originalDomainStrongMap_pullback` identifies all its admissible
bounded maps with the original atlas restrictions.
`originalDomainStrongMap_pullback_selected` recovers the bounded identity
at the chosen target copy of each source chart, identifying it with the
corresponding pullback of the already constructed chosen domain map.
`originalDomainStrongMap_restrict` proves direct source restriction
transitivity. `restrictDomains_id` and `originalDomainStrongMap_id`
recover the full identity for S=T. These are full strong-map equalities,
without a general strong-map composition operation.

The chartwise hypothesis is not derived from pointwise containment for
general maps. Arbitrary original-domain inverse-image existence, atlas
saturation, unrestricted strong-map composition, structure sheaves,
and analytic étale sites remain separate obligations.
