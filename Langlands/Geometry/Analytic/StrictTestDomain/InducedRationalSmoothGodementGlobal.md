# Global Godement pullback and support comparison on induced rational spectra

This module constructs global section complexes, their homology, and
actual contravariant spatial maps for full smooth coefficients on the
existing induced rational spectra. It also constructs the compact-to-global
support transformations and proves their naturality under every proper
induced rational transport map.

The complete ultrametric normed field `K`, its presented strict affinoid
algebra `P`, the topological group `G`, commutative coefficient ring `R`,
and coefficient module carriers share universe `u`. Fix the existing
`RationalSpectralAction G P`. Objects are the actual
`OpenSubgroupTransport` objects; their `InducedSpectrum` spaces are the
constructed balanced quotients with their existing actions and topologies.
`HasStableNeighbourhoods G X.InducedSpectrum` is explicitly assumed at
every space used. This module does not prove it for arbitrary rational
transport data.

All coefficient objects and intertwiners in `SmoothRep R G` are retained.
The sheaf is the full ordinary-open locally constant smooth coefficient
sheaf, without a topology or a finite-dimensionality condition on the
coefficient module. The resolution used here is the existing separate
smooth Godement complex.

In `OpenSubgroupTransport.SmoothCohomology`,
`godementGlobalComplex X` is the actual `sheafFunctor X` followed by
`smoothGodementGlobalComplex R G X.InducedSpectrum`. It takes all global
sections in each degree, with the original differential and algebraic
`G` action. Its codomain is cochain complexes in `Rep R G`.
`godementGlobalCohomology X q` applies actual algebraic-representation
homology in degree `q : ℕ` to that complex.

`godementForgetSupportComplex X` specializes the existing natural
compact-support inclusion at the full coefficient sheaf. Its source is
the existing `godementCompactComplex X`, followed by degreewise
`SmoothRep.toRep`, and its target is `godementGlobalComplex X`.
The original-section formula is precisely `s ↦ s.val`.

`godementForgetSupport X q` specializes the existing cohomology support
transformation. Its source is `godementCompactCohomology X q` followed
by `SmoothRep.toRep`; its target is `godementGlobalCohomology X q`.
The component theorem gives the inverse exact-inclusion homology
comparison followed by homology of `godementForgetSupportComplex X`.
Exactness of the smooth-representation inclusion is already proved in
the imported construction.

In `OpenSubgroupTransport.Hom`,
`godementGlobalPullbackNatTrans f` specializes
`Spatial.coefficientGlobalNatTrans` to the actual continuous map
`f.inducedMap` and its proved equivariance. No properness hypothesis is
needed for this global pullback. Its component first applies the global
Godement functor on `Y` to the full coefficient sheaf pullback, then the
constructed global spatial chain map. Its original-section formula
holds in every chain degree, using the resolved coefficient map and
the actual degreewise spatial sheaf map at the top open, with the
smooth-image witness removed.

The naturality theorem retains every original coefficient intertwiner.
The identity theorem uses `SheafVariation.inducedMap_id_eq`, followed by
generic congruence and the coefficient global identity equation. The
composition theorem uses `SheafVariation.inducedMap_comp_eq` and the
generic strict coefficient global equation to prove

```text
pullback(f ≫ g) = pullback(g) ≫ pullback(f).
```

These are equalities for the actual induced transport maps, without any
chosen comparison data or an assumed inverse to the lax direct-image
comparison.

`godementGlobalCohomologyPullbackNatTrans f q` is homology of the
constructed global chain transformation in `Rep R G`. Its component,
coefficient naturality, identity and strict composition formulas are
proved by applying the homology functor to the chain maps and their
equations. Thus maps are constructed in every nonnegative degree,
natural in all original coefficient morphisms.

For `hf : IsProperMap f.inducedMap`,
`godementCompactPullbackNatTrans_forgetSupport` compares the existing
proper compact chain pullback with the new global chain pullback.
The left side applies degreewise `SmoothRep.toRep` to the compact
pullback and then forgets support on `X`; the right side first forgets
support on `Y` and then pulls back globally. The theorem specializes
the actual coefficient support square proved in `CoefficientGlobal`.
Its `_natTrans` version packages the same square as an equality of
full coefficient natural transformations.

`godementCohomologyPullbackNatTrans_forgetSupport` is the corresponding
square for compact and global homology. It retains the
`SmoothRep.toRep` inclusion on compact cohomology and the exact-inclusion
support comparison just described. Its `_natTrans` version again gives
the equality for the full coefficient functors. Properness is used
only where compact pullback occurs; an arbitrary rational transport
morphism is not asserted to be proper.

This is an internal specialization of actual spectra, coefficient
sheaves, global spatial maps, support transformations and categorical
homology. The generic coefficient maps and support squares are implemented
in `Langlands/Cohomology/SmoothGodement/CoefficientGlobal`. Their proved
formulas and the actual induced-map equations justify this specialization.
No new external literature assertion is attributed to it.

The construction does not identify these objects with higher right
derived cohomology, prove acyclicity or resolution exactness, compare
the separate smooth and full equivariant Godement routes, commute
invariants with homology, or identify degree-zero spatial maps with
separately transported maps. Analytic etale cohomology, uniformization,
Shimura realization and the full Harris compatibility remain separate
obligations.
