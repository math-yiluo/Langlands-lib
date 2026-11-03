# The locally ringed space of an actual affinoid spectrum

Author: Worker 36.

Let `K` be a complete ultrametric normed field and let `A` be a
`PresentedAffinoidAlgebra K`, with its actual closed positive-polyradius Tate
quotient algebra. This module constructs

```text
locallyRingedSpace K A : AlgebraicGeometry.LocallyRingedSpace.
```

Its underlying topological space is `BanachSpectrum A`. Its structure sheaf is
the concrete compatible-family sheaf on ordinary open subsets, with scalars
forgotten. Its stalks are proved local by comparison with the ordinary-open
algebra stalks constructed in `RationalOpenStalkResidue` and proved local in
`RationalOpenLocalRing`.

## The ring-valued structure sheaf

`openRingPresheaf K A` is the composite of `openAlgebraPresheaf K A` with
`forget₂ (CommAlgCat K) CommRingCat`. Thus it retains the original rings of
compatible rational-chart families and the original restriction maps.

The module proves locally that this forgetful functor preserves limits. It
identifies it with the equivalence from commutative `K`-algebras to commutative
rings under `K`, followed by the functor forgetting the under-object map.
Pinned Mathlib supplies limit preservation for that composite.
`openRingPresheaf_isSheaf` then applies
`CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf` to the published algebra-sheaf
law. `ringSheafedSpace K A` stores this specific sheaf on this specific spectrum.

## The actual stalk comparison

`openStalkRingIso x` is a canonical isomorphism in `CommRingCat`:

```text
(forget₂ (CommAlgCat K) CommRingCat).obj (openStalk x)
  ≅ TopCat.Presheaf.stalk (openRingPresheaf K A) x.
```

Both stalks use the diagram of ordinary open neighborhoods of the same actual
point `x`. The isomorphism is `preservesColimitIso` for this diagram.
The module proves the needed filtered-colimit preservation by the same
equivalence with rings under `K`: filtered categories are connected, and the
under-object forgetful functor preserves connected colimits in pinned Mathlib.

`openGerm_openStalkRingIso` records the exact comparison with the existing germ
maps. For every ordinary open `U`, actual point `x`, and `hx : x ∈ U`, forgetting
the scalar structure of `openGerm U x hx` and composing with the comparison
isomorphism equals the ordinary ring-presheaf germ:

```text
forget₂.map (openGerm U x hx) ≫ (openStalkRingIso x).hom
  = TopCat.Presheaf.germ (openRingPresheaf K A) U x hx.
```

The proof is the colimit-injection equation
`ι_preservesColimitIso_hom`. The declaration also generates its reassociated
form for composition with subsequent morphisms.

## Locality and provenance

`locallyRingedSpace K A` has `ringSheafedSpace K A` as its sheafed space.
For each actual point, the already proved `openStalk_isLocalRing x` supplies
the source local-ring instance, whose carrier is unchanged by forgetting scalars.
The ring equivalence of `openStalkRingIso x` transfers this instance to the actual
ring-valued structure-sheaf stalk via `RingEquiv.isLocalRing`. Consequently
the `isLocalRing` field is derived from the constructed stalk and its proved
unit criterion.

This is an internal construction from `RationalOpenGluing`,
`RationalOpenStalkResidue`, `RationalOpenLocalRing`, and the pinned Mathlib
limit, colimit, sheaf, and locally ringed-space APIs. In Mathlib the relevant
sources are `Algebra/Category/CommAlgCat/Basic`,
`CategoryTheory/Limits/Constructions/Over/Connected`,
`CategoryTheory/Limits/Preserves/Limits`,
`CategoryTheory/Sites/Sheaf`, and `Geometry/RingedSpace/LocallyRingedSpace`.
No new original-literature assertion is claimed.

The construction allows trivial valuations, arbitrary positive polyradii and
nilpotent quotient algebras. No nonzero-algebra assumption is imposed. Locality
is point-indexed, so the empty spectrum is included.

This module packages the ordinary-open sheaf as a locally ringed space. It does
not yet construct the functor on all bounded affinoid morphisms, identify stalk
residue fields with completed residue fields, compare with all-closed-chart
stalks or stored general-domain sheaves, construct general analytic atlases, or
construct analytic etale or equivariant sites.
