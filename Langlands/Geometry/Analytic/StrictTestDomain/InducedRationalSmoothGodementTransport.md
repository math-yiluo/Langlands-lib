# All-degree smooth Godement pullback on actual induced rational spectra

This module constructs proper spatial maps on the existing compact smooth
Godement complexes and all their homology objects on actual induced rational
spectra. It specializes the generic construction in
`Langlands/Cohomology/SmoothGodement/CoefficientSpatial` to
`OpenSubgroupTransport.Hom.inducedMap`.

The complete ultrametric normed field `K`, its presented strict affinoid
algebra `P`, the topological group `G`, coefficient ring `R`, and coefficient
module carriers share universe `u`. The ring is any commutative ring.
Fix the existing `RationalSpectralAction G P`. Objects `X`, `Y`, `Z` are
actual objects of its `OpenSubgroupTransport` category. The spaces
`X.InducedSpectrum` are the previously constructed balanced quotient
spectra, with their existing topologies and actions. The module assumes
`HasStableNeighbourhoods G X.InducedSpectrum` at every space used; it does
not prove this property for arbitrary rational transport data.

A morphism `f : X ⟶ Y` supplies the actual continuous equivariant map
`f.inducedMap`. The additional hypothesis is `IsProperMap f.inducedMap`.
It is retained throughout compact pullback. In particular, arbitrary
rational transport morphisms are not asserted to be proper.

`godementCompactPullbackNatTrans f hf` has source
`SmoothCohomology.godementCompactComplex Y` and target
`SmoothCohomology.godementCompactComplex X`. It is the generic
`coefficientCompactNatTrans` for `f.inducedMap`, its proved equivariance,
and `hf`. These are the existing complexes of compact sections of the
separate smooth Godement complex of the **full** locally constant smooth
coefficient sheaf. Every smooth coefficient representation and its original
intertwiners remain in the functor domain.

`godementCompactPullbackNatTrans_app` states that the component at `M`
first applies the `Y` compact smooth Godement functor to
`SmoothDirectImage.coefficientMap f.inducedMap f.inducedMap_smul M`,
then applies the proper spatial chain map to the actual coefficient sheaf
on `X`. `godementCompactPullbackNatTrans_apply` gives the original compact
section formula in every degree: apply the resolved coefficient map,
then the actual spatial sheaf map at the top open, and remove its
smooth-image witness. The chain naturality theorem is the square for
every original coefficient intertwiner.

The identity theorem uses
`SheafVariation.inducedMap_id_eq X` to replace the actual continuous map
of `𝟙 X` by `ContinuousMap.id X.InducedSpectrum`. The generic equality
lemma changes neither chain transformation nor its source and target
coefficient complexes. The generic coefficient identity then gives the
identity chain map.

The composition theorem uses
`SheafVariation.inducedMap_comp_eq f g`, identifying the actual continuous
map of `f ≫ g` with `g.inducedMap.comp f.inducedMap`. The generic
coefficient composition equation then proves

```text
pullback(f ≫ g) = pullback(g) ≫ pullback(f).
```

The properness witness is the already proved
`isProperMap_inducedMap_comp f g hf hg`; proof irrelevance reconciles it
with properness of the composite continuous maps. This equation uses
the actual transport maps and requires no chosen comparison isomorphism.

`godementCohomologyPullbackNatTrans f hf q` applies homology in
`SmoothRep R G` to the constructed compact chain transformation. Its
source and target are the already defined
`SmoothCohomology.godementCompactCohomology` functors in degree `q`.
The component theorem identifies it with homology of the actual chain
map. Naturality holds for all coefficient intertwiners. The identity and
contravariant composition equations follow by mapping the chain equations
through the homology functor.

This module is an internal specialization, justified by the exact
definitions of the imported actual spectra, transport maps, coefficient
sheaves, compact complexes and homology. It introduces no new external
source assertion. It extends the available constructions to all degrees,
but does not prove equality in degree zero with the map
`godementZeroPullback` defined by transport through the compact-function
isomorphism in `InducedRationalSmoothCohomologyTransport`.

No higher right derived pullback, Godement acyclicity or resolution
exactness, comparison between the separate smooth and full equivariant
Godement routes, invariant exactness, etale cohomology, uniformization,
Shimura realization or Harris compatibility is asserted. Those comparisons
and the full geometric specialization remain explicit obligations of the
wider framework.
