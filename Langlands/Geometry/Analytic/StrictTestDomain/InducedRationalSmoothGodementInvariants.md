# Invariant compact Godement pullback on actual induced rational spectra

This module constructs proper spatial maps on the existing invariant compact
Godement complexes and their module homology on induced rational spectra.
It imports and reuses `InducedRationalInvariantComplex`, and specializes
the proper full coefficient chain maps of
`SmoothGodement.CoefficientInvariants` to the actual continuous equivariant
maps `OpenSubgroupTransport.Hom.inducedMap`.

The complete ultrametric normed field `K`, presented strict affinoid algebra
`P`, topological group `G`, commutative coefficient ring `R` and coefficient
module carriers share universe `u`. Fix `ρ : RationalSpectralAction G P`.
Objects `X`, `Y`, `Z` belong to its existing `OpenSubgroupTransport`
category. Their `InducedSpectrum` spaces are the constructed balanced
quotients of local Banach spectra, with the existing topologies and actions.
Each space used has the explicit hypothesis
`HasStableNeighbourhoods G X.InducedSpectrum`.

A morphism `f : X ⟶ Y` supplies the actual continuous map `f.inducedMap`
and its proved equivariance. Compact pullback also requires the explicit
hypothesis `hf : IsProperMap f.inducedMap`. The module does not prove this
hypothesis or stable neighbourhoods for arbitrary rational transport data.
Coefficients range over all of `SmoothRep R G`, with all original
intertwiners, through the existing full locally constant smooth sheaf
functor `SmoothCohomology.sheafFunctor` on ordinary opens.

The imported `InducedRationalInvariantComplex` supplies
`SmoothCohomology.godementInvariantCompactComplex X`, its module homology
`godementInvariantCompactCohomology X q`, and its degree-zero isomorphism
with `invariantCompactFunctions X`. These existing definitions are reused
without modification. Write `I = SmoothGodementComparison.smoothInvariants
R G` for whole-group invariants and `I_*` for its degreewise extension.

In `OpenSubgroupTransport.SmoothCohomology`, the new
`godementInvariantCompactComplexIso X` is the actual natural isomorphism

```text
godementCompactComplex X ⋙ I_* ≅ godementInvariantCompactComplex X.
```

It is `Functor.isoWhiskerLeft` of the generic comparison from
`SmoothGodement.InvariantSpatial`. That comparison is constructed from
Mathlib's composition isomorphism for functors on homological complexes;
it acts identically on the underlying invariant compact sections.
The construction uses termwise invariants before module homology, and
introduces no additional degree-zero isomorphism.

In `OpenSubgroupTransport.Hom`,
`godementInvariantCompactPullbackNatTrans f hf` has source the invariant
complex functor on `Y` and target that on `X`. It specializes
`coefficientInvariantCompactNatTrans` to `f.inducedMap`.
The component formula first resolves
`SmoothDirectImage.coefficientMap f.inducedMap f.inducedMap_smul M` and
then applies the actual invariant spatial chain map to the full coefficient
sheaf on `X`.

The theorem ending in `_app_eq_map` identifies this component with
`I_*.map` of the previously constructed
`godementCompactPullbackNatTrans f hf`. The theorem ending in `_f` gives
the corresponding equality in each degree. The theorem ending in `_apply`
says that removing the invariant witness gives the existing compact chain
map applied to the original invariant compact section. The full coefficient
naturality square retains every original coefficient intertwiner.

`godementInvariantCompactPullbackNatTrans_comparison` proves equality of
the natural transformations around the chain comparison square: applying
`I_*` to compact pullback and then the comparison on `X` equals the
comparison on `Y` followed by invariant pullback. The proof uses
extensionality in coefficient object, degree and section; each comparison
acts identically on the underlying sections.

Identity uses `SheafVariation.inducedMap_id_eq X` and the generic map
congruence and identity theorems. Composition uses
`SheafVariation.inducedMap_comp_eq f g`, its actual properness witness
`isProperMap_inducedMap_comp f g hf hg`, and the generic strict coefficient
composition theorem. It proves

```text
pullback(f ≫ g) = pullback(g) ≫ pullback(f).
```

`godementInvariantCohomologyPullbackNatTrans f hf q` applies module homology
to this actual invariant chain transformation. Its component theorem gives
that formula explicitly. All coefficient intertwiners commute with it,
and its identity and strict contravariant composition laws follow by
homology functoriality from the chain equations.

This is an internal specialization of the actual spectra, coefficient
sheaves, compact Godement complexes, whole-group invariants and proper
spatial maps already constructed in the imported modules. It introduces
no external-source assertion. Invariants are taken termwise before module
homology. Exactness of invariants, commutation with compact homology,
higher right-derived identification, Godement acyclicity or resolution
exactness, spatial compatibility of the degree-zero identifications,
comparison with the full equivariant Godement route, and analytic etale,
uniformization, Shimura and Harris realization remain separate obligations
of the wider framework.
