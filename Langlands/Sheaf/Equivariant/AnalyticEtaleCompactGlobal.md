# Compact and ordinary étale cohomology on a compact analytic space

This internal construction uses the Library's actual functors
`etaleCompactSections`, `etaleSections`, `etaleCompactCohomology`, and
`etaleCohomology`. Its parameters are the complete ultrametric base field `K`,
a normed extension field `L`, an analytic space `X`, point axioms `h` for all
`L`-valued points, and a commutative ring `R` in the same universe as these
cohomology functors. No group action is involved.

`etaleCompactSectionsInclusion` is the natural inclusion from compactly
supported sections to all sections, obtained by applying the generic
`PointSupport.compactSectionsι` to the presheaf underlying a sheaf. Its component
sends a section in the compact-support submodule to its underlying section.

Suppose `|X|` is compact and `pointProjection L X` is surjective.
`isCompactlySupported_etalePoints_of_compactSpace` proves that every section of
any module presheaf over any étale object has compact support, in the Library's
sense that its support lies in a compact set of the point index space. The
existing induced-topology compactness criterion reduces this to containment of
the projected support in a compact subset of `|X|`; choose the whole space.
Neither Hausdorffness nor openness of étale maps is required for this argument.

The inclusion is therefore bijective on each sheaf: injectivity is that of the
submodule inclusion and surjectivity follows by equipping each section with the
compact-support proof. This gives `etaleCompactSectionsIsoOfCompactSpace`, whose
forward map is the inclusion.

`etaleCompactCohomologyIsoOfCompactSpace` derives the forward and inverse natural
transformations using `NatTrans.rightDerived`. Preservation of composition and
identities proves the two inverse laws. This yields natural isomorphisms
`H_c^q(X, -) ≅ H^q(X, -)` for every natural number `q`. The final lemma transports
`IsZero` across their components, giving an equivalence of vanishing in each
degree for every sheaf.

The provenance is internal: all arguments use the published point topology,
compact-support definitions, and right-derived functor API. No equivariant
cohomological comparison or acyclicity assertion is assumed.
