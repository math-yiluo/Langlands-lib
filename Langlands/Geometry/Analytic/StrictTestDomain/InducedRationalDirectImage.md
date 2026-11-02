# Full sheaf variation along actual induced rational transport

This module constructs direct images of full ordinary-open equivariant sheaves
along every morphism of the actual rational open-subgroup transport category.
It also constructs precomposition of all locally constant coefficient sections,
natural in every original coefficient intertwiner, with identity, composition
and ambient structural-map compatibility. This is a progressive construction
within the wider Harris framework task; that task remains incomplete.

The namespace is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.SheafVariation`.

## Provenance

This is an internal construction from the existing actual rational spectra and
`Langlands.Sheaf.Equivariant.DirectImage`. The rational-spectrum module already
constructs the continuous maps, proves their full-group equivariance, and proves
their identity, composition and ambient-map equations. The generic direct-image
module constructs inverse-open precomposition, proves the ordinary sheaf
condition using Mathlib, and proves coefficient naturality on every labelled
arrow and every original coefficient intertwiner. Here these constructions are
specialized to the original rational maps. Equalities of those maps give the
comparison isomorphisms, and the generic coefficient laws give their
compatibilities. No new original-literature assertion or assumed comparison is
introduced.

## Inputs, universes and scope

The general section has a complete normed ultrametric field `K : Type u`, a
presented strict affinoid algebra `P` over it, a topological group `G : Type v`,
and a `RationalSpectralAction G P`. Its objects `X`, `Y`, `Z` are the existing
`OpenSubgroupTransport` objects, each containing an actual open subgroup and
invariant rational quotient. `X.LocalSpectrum` is the Banach spectrum of that
quotient algebra with its constructed subgroup action. `X.InducedSpectrum` is
the actual balanced quotient `G ×_H X.LocalSpectrum`, in universe `max u v`.
The actions and their joint continuity are the existing constructed ones.

For general sheaves, the coefficient category `A : Type a` has morphisms in
universe `b`. No completeness or cocompleteness premise is imposed. For
coefficients, `R : Type r` is an arbitrary commutative ring and `M : Type w` is
an arbitrary `R`-module. The coefficient functors have domain `Rep.{w} R G`
and section category `ModuleCat.{max (max u v) w} R`. All these universes remain
independent.

Only the ambient section aligns the field and group universes to `u`. Then both
the induced spectrum and ambient Banach spectrum lie in universe `u`, and their
coefficient section category is `ModuleCat.{max u w} R`. The coefficient ring
and module universes remain independent. No universe-lifting comparison is
claimed.

There is no coefficient topology, finite-dimensionality, subgroup normality,
local compactness, separation, total disconnectedness, compactness or
stable-neighbourhood hypothesis. These are ordinary-open equivariant sheaves.
No general preservation of smoothness is asserted.

## The actual inverse opens and full sheaf direct image

For a rational transport morphism `f : X ⟶ Y`, the imported construction is the
actual continuous full-group-equivariant map

```text
f.inducedMap : X.InducedSpectrum → Y.InducedSpectrum
[a,x] ↦ [a * f.label⁻¹, f.localSpectrumMap x].
```

Here `f.localSpectrumMap` is the spectrum pullback of the original bounded
rational restriction. The inverse label is part of the existing spatial map.
`inducedMap_id_eq` and `inducedMap_comp_eq` promote its pointwise identity and
composition equations to equalities of continuous maps.

`preimage f` sends an open `U` to its actual inverse image under
`f.inducedMap`. `mem_preimage` gives the membership equivalence, and
`inducedMk_mem_preimage` exposes the displayed representative formula.
`preimage_map_label` states that every full-group transport label is retained.
Its arrow condition follows from the original full-group equivariance, rather
than from an assumed map between sheaf categories.

`directImage A f` is the entire generic sheaf direct image along this map. At
an arbitrary target open `U`, its section object is the original section object
over `f⁻¹(U)`. A labelled arrow is sent to the original labelled restriction on
those inverse opens, and every sheaf morphism is evaluated at the same inverse
open. The three equations `directImage_obj_obj`, `directImage_obj_map` and
`directImage_map_app` are reflexive identifications of these data. Nothing
selects a submodule or a subfamily of morphisms.

`toSheafIso` identifies forgetting equivariance after this direct image with
ordinary `TopCat.Sheaf.pushforward` after forgetting equivariance. Its components
are identities. The imported generic sheaf construction supplies the full
ordinary sheaf condition, using inverse images of arbitrary open covers.

`directImageIdIso` compares identity rational transport with the identity sheaf
functor. `directImageCompIso f g` has direction

```text
directImage (f ≫ g) ≅ directImage f ⋙ directImage g.
```

These use the proved equalities of the actual continuous maps. The private
helper `directImage_congr` proves that equal continuous equivariant maps give
the same entire direct-image functor by substituting the map equality; the
remaining equivariance proofs are proof-irrelevant. The comparisons are
`eqToIso` of those equalities. The generic identity and composite direct images
have the required endpoint functors definitionally. This module does not claim
additional coherence identities between these isomorphisms.

## Full coefficient sections and original intertwiners

For a representation `τ` on `M`, `coefficientMap f τ` is a morphism from the full
coefficient sheaf on `Y.InducedSpectrum` to the direct image of the full
coefficient sheaf on `X.InducedSpectrum`. At `U` it precomposes every locally
constant section with the restricted continuous map from `f⁻¹(U)` to `U`.
`coefficientMap_apply` exposes this formula using the actual
`DirectImage.pointMap`. `coefficientMap_mk_apply` states it on representatives:

```text
s ↦ ( [a,x] ↦ s([a * f.label⁻¹, f.localSpectrumMap x]) ).
```

For a labelled arrow `k`, both paths in sheaf naturality retain the original
inverse coefficient operator `τ(k.label⁻¹)`. Their point maps agree by
`f.inducedMap_smul`. This is the imported generic coefficient-map construction;
it applies to every section, every open and every labelled arrow.

`coefficientFunctor X R` is the existing full locally constant coefficient-sheaf
functor at `X`. `coefficientFunctor_map_app` identifies its action on each
original intertwiner `c` with the pointwise map `s(z) ↦ c(s(z))`.
`coefficientNatTrans f` has endpoints

```text
coefficientFunctor Y R ⟶
  coefficientFunctor X R ⋙ directImage f.
```

Its components are `coefficientMap f`, and its naturality quantifies over all
morphisms of `Rep.{w} R G`. The original coefficient carrier and linear maps are
retained throughout.

`coefficientMap_id` says that the map for identity transport, followed by the
component of `directImageIdIso`, is the identity on the original full coefficient
sheaf. `coefficientMap_comp` says that the map for `f ≫ g`, followed by the
component of `directImageCompIso`, equals the map for `g` followed by `g` direct
image applied to the map for `f`. The private `coefficientMap_congr` proves
compatibility with equal continuous maps by substitution and the category
identity law. Composing it with the generic coefficient identity or composition
law proves the stated laws. Thus these equations include the necessary endpoint
transport for the actual rational maps, which need not be definitionally the
identity or composite maps.

## The common ambient spectrum

In the common field/group universe section, `ambientDirectImage A X` is direct
image along the actual full-group-equivariant structural map `X.ambientMap`
into `AmbientSpectrum ρ`. The imported representative formula is

```text
X.ambientMap [a,x] = a • X.localToAmbient x.
```

`ambientDirectImageIso f` compares
`directImage A f ⋙ ambientDirectImage A Y` with `ambientDirectImage A X`.
It uses the proved equality of continuous maps
`Y.ambientMap.comp f.inducedMap = X.ambientMap`, promoted from the original
pointwise structural-map equation. As above, the comparison is `eqToIso` of the
full functor equality.

`ambientCoefficientMap X τ` precomposes every ambient coefficient section along
`X.ambientMap`. `ambientCoefficientNatTrans X` makes this natural in all
original coefficient intertwiners. Finally `ambientCoefficientMap_transport`
proves that first using the ambient coefficient map for `Y`, then direct image
of `coefficientMap f`, then the ambient functor comparison gives the original
ambient coefficient map for `X`. The proof composes the generic coefficient
composition law with `coefficientMap_congr` for the structural-map equality.

## Remaining boundaries

These are full ordinary-open sheaf direct images and coefficient maps varying
in actual rational transport objects. The coefficient maps are not claimed to
be isomorphisms for arbitrary rational morphisms. Smooth direct images, compact
support, supported Godement complexes, higher derived comparisons,
analytic/etale identification, arithmetic towers and the required Harris
specialization remain wider-task obligations. No such comparison or desired
cohomology group is supplied as an assumed field of this construction.
