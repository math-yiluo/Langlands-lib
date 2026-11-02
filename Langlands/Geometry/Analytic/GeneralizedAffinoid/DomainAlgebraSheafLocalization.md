# Localization of the actual stored full-domain algebra sheaf

Let `K` be a complete ultrametric normed field, `A` an actual presented
affinoid algebra over `K`, and `d : Domain K A` a full represented affinoid
domain. This module identifies the stored algebra sheaf under the finite-site
equivalence from `DomainSiteLocalization`.

`relativeAlgebraSheaf d` is the image of `algebraSheaf K d.algebra` under
`d.localizationSheafEquivalence (CommAlgCat K)`. On a slice object
`U : Over d`, its value is the original algebra `U.left.algebra`. On a slice
arrow `f : U ⟶ V`, its restriction is exactly `f.left.restriction`.
These equations include the actual algebras and maps. At the level of the
bounded algebra presheaves, `relative_boundedPresheaf` states the equality of
the entire functors; `relative_algebraPresheaf` states the corresponding
equality after forgetting the norms and presentations.

`localizationAlgebraSheafIso d` is an isomorphism

```text
relativeAlgebraSheaf d ≅ (algebraSheaf K A).over d.
```

Both component directions are the identity on each retained algebra.
The relative structural map at `U` is the original bounded restriction
`U.hom.restriction : d.algebra → U.left.algebra`.
The two structural-map formulas identify this map on every section in both
directions of the comparison.

The inverse equivalence also recovers the original sheaf:

```text
(d.localizationSheafEquivalence (CommAlgCat K)).inverse.obj
    ((algebraSheaf K A).over d) ≅ algebraSheaf K d.algebra.
```

This is `inverseLocalizationAlgebraSheafIso d`. Its component directions are
identities. The equalities `extend_boundedPresheaf` and
`extend_algebraPresheaf` include every restriction map in the inverse
transport. Restriction along `d.extendInclusion U` is exactly `U.baseMap`;
the final formula retains this equality after the inverse sheaf comparison.

The construction is an internal consequence of published modules.
`DomainRelativeRepresentation` and `DomainLocalization` retain the algebras
and bounded maps literally in both localization functors.
`DomainAlgebraSheaf` proves sheafness of the actual stored algebra presheaf,
and `DomainSiteLocalization` proves the equivalence for the independently
constructed finite domain topologies. Consequently the compared presheaves
are definitionally equal. Each displayed sheaf isomorphism lifts the identity
presheaf isomorphism with `ObjectProperty.isoMk`; the section formulas and
functor equalities are reflexive. No new assertion is attributed to original
literature.

The scope is the finite point-covering site of full represented domains over
one affinoid and its slice. All positive polyradii, trivial valuations,
nilpotents, zero algebras, empty spectra and permitted empty finite covers
remain supported by the imported constructions. This unit does not construct
unrestricted analytic atlases, the full analytic G-topology, or etale,
quasi-etale, equivariant and Harris-tower sites.
