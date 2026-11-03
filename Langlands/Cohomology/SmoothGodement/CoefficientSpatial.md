# Proper spatial maps on full smooth coefficient Godement complexes

This module constructs compact chain pullbacks and their homology maps for
the full locally constant smooth coefficient sheaves. It combines
`SmoothDirectImage.coefficientNatTrans` with the actual proper compact
spatial transformation in `SmoothGodement/Spatial`. The resulting maps are
strictly contravariant in proper spatial maps and natural in every original
coefficient intertwiner.

The coefficient ring `R`, group `G`, spaces and representation carriers share
universe `u`. The ring is commutative. The group is a topological group.
Each space has a `G` action, continuous fixed translations
(`ContinuousConstSMul`) and `HasStableNeighbourhoods`. A spatial map
`f : C(X, Y)` is equivariant and has a supplied proof `IsProperMap f`.
The coefficients are arbitrary objects of `SmoothRep R G`, without a
topology on the coefficient modules.

Write `L_X` for `LocallyConstantSheaf.smoothFunctor R G X`, `C_X` for
`smoothGodementCompactComplex R G X`, and `D_f` for the actual smooth
direct-image functor. The sheaves are ordinary-open equivariant module
sheaves. The separate smooth Godement complex used in `C_X` is the
constructed smooth-zero/cokernel complex.

For every coefficient object `M`, the already constructed coefficient map is

```text
c_f(M) : L_Y(M) → D_f(L_X(M)).
```

`coefficientCompactNatTrans f hf hp` is the composite natural transformation
from `L_Y ⋙ C_Y` to `L_X ⋙ C_X` whose component is

```text
C_Y.map(c_f(M)) ≫ compactMap f hf hp (L_X(M)).
```

The first factor applies the actual smooth Godement compact-complex functor
to the full coefficient sheaf map. The second is the constructed proper
spatial chain map. Neither factor is supplied as arbitrary comparison data.
`coefficientCompactNatTrans_app` records this equation.

`coefficientCompactNatTrans_f` gives the corresponding composite in every
degree. `coefficientCompactNatTrans_apply` describes its underlying original
section: first apply the resolved coefficient map, then the degreewise
`Godement.SmoothSpatial.complexMap` at the top open, and finally remove its
smooth-image subtype witness. Compact support is retained by the already
constructed proper pullback. The formula makes no claim that a higher
Godement section is an original locally constant coefficient function.

`coefficientCompactNatTrans_f_zero` identifies the degree-zero chain
component with compact sections of the smooth-zero coefficient map,
followed by compact sections of the actual spatial zero map and the proper
compact-section pullback. This concerns the zero term of the complex.
It is not an identification of the induced degree-zero homology map with a
separately transported map.

`coefficientCompactNatTrans_naturality` is the commuting chain square for
every `M ⟶ N` in `SmoothRep R G`. Its reassociated form is also available.

`coefficientCompactNatTrans_id` proves that the identity spatial map gives
the identity coefficient chain transformation. The proof replaces the
coefficient identity map by the actual smooth-direct-image unit and applies
`compactMap_id`.

`coefficientCompactNatTrans_comp` proves that the transformation for
`g.comp f` equals the transformation for `g` followed by that for `f`.
The coefficient composition law introduces
`SmoothDirectImage.compMap f hf g hg`. After applying `C_Z`, this is exactly
the factor appearing in `compactMap_comp`. That equation replaces the
composite spatial map by the two individual spatial maps. Naturality of
the second spatial transformation moves the intermediate coefficient map
to its required position. Thus the final coefficient transformations
compose strictly without assuming that the lax direct-image comparison is
invertible.

`coefficientCompactNatTrans_congr` proves invariance under equality of the
original continuous maps. Its proof substitutes that equality; proof
irrelevance identifies the equivariance and properness witnesses.

For `q : ℕ`, `coefficientCohomologyNatTrans f hf hp q` is obtained by
whiskering the constructed coefficient chain transformation with the
homology functor in `SmoothRep R G`. Its source is
`L_Y ⋙ smoothGodementCompactCohomology R G Y q` and its target is the
corresponding functor on `X`. `coefficientCohomologyNatTrans_app` gives the
homology-map formula. Its identity and strict composition theorems follow
by applying homology to the proved chain equations and using functoriality.
The definition as a natural transformation retains every coefficient
intertwiner in every degree.

This is an internal construction from the imported actual coefficient
sheaf maps, spatial chain maps and homology functor. No new external
literature assertion is attributed to it. It does not assert resolution
exactness, compact-section acyclicity, identification with a right derived
functor, exactness of taking invariants, comparison with the full
equivariant Godement route, or analytic, etale or arithmetic realization.
The full Harris specialization remains a separate obligation.
