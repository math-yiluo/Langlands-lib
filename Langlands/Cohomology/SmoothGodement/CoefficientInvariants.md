# Invariant compact Godement maps for full smooth coefficients

This module constructs proper spatial chain transformations for the invariant
compact smooth Godement complexes of the full locally constant smooth
coefficient sheaves. It then applies module homology. Its declarations are in
`Langlands.Cohomology.SmoothGodementCohomology.Spatial`.

The commutative ring `R`, topological group `G`, spaces `X`, `Y`, `Z` and
coefficient carriers share universe `u`. Each space has a `G`-action with
continuous fixed translations and `HasStableNeighbourhoods`. The continuous
map `f : C(X, Y)` is equivariant by `hf` and proper by `hp : IsProperMap f`.
A second map `g : C(Y, Z)` has corresponding witnesses `hg` and `hq`.
The coefficient category is the full category `SmoothRep R G`; every object
and original intertwiner is retained. The sheaves are on the ordinary-open
transport category, with no coefficient topology or finite-dimensionality
restriction.

Write `L_X = LocallyConstantSheaf.smoothFunctor R G X`,
`C_X = smoothGodementCompactComplex R G X`, and
`V_X = smoothGodementInvariantCompactComplex R G X`. The functor

```text
I = SmoothGodementComparison.smoothInvariants R G
  = SmoothRep.toRep ⋙ Rep.invariantsFunctor R G
```

takes whole-group invariants, and `I_*` denotes its degreewise extension to
cochain complexes indexed by `ℕ`. The existing `InvariantSpatial` module
constructs the comparison `C_X ⋙ I_* ≅ V_X` and the proper invariant spatial
map `invariantCompactMap f hf hp`.

`coefficientInvariantCompactNatTrans f hf hp` has type

```text
L_Y ⋙ V_Y ⟶ L_X ⋙ V_X.
```

It first applies `V_Y` to the actual full coefficient sheaf transformation
`SmoothDirectImage.coefficientNatTrans f hf`, then uses the invariant
compact spatial transformation, whiskered with `L_X`. At each coefficient
object `M`, `coefficientInvariantCompactNatTrans_app` gives the composite

```text
V_Y.map(SmoothDirectImage.coefficientMap f hf M)
  ≫ invariantCompactMap f hf hp (L_X.obj M).
```

Thus the source is the full coefficient sheaf on `Y`, rather than an
arbitrary sheaf supplied in the image of direct image.

`coefficientInvariantCompactNatTrans_app_eq_map` proves that this component
is exactly `I_*.map((coefficientCompactNatTrans f hf hp).app M)` on the
existing presentations. Its proof is extensionality in the complex degree
and invariant section. The comparison of composed functors acts identically
on these sections. The theorem `coefficientInvariantCompactNatTrans_f`
therefore identifies every term with `I.map` of the corresponding compact
chain map. For an invariant compact section `s`, the theorem ending in
`_apply` states that removing the invariant witness from its image gives
`SmoothRep.hom` of that compact chain map on `s.val`. Its compact-support
witness remains in place. Properness and equivariance are inherited from
the constructed compact map.

`coefficientInvariantCompactNatTrans_naturality` is the commuting chain
square for every original intertwiner `a : M ⟶ N`. Identity follows by
expanding the component, identifying the coefficient identity with the
smooth-direct-image unit, and applying `invariantCompactMap_id`.
For composition, expand `SmoothDirectImage.coefficientMap_comp`, apply
functoriality of `V_Z`, and use `invariantCompactMap_comp` and spatial
naturality. The coefficient and spatial equations use the same actual lax
direct-image comparison. This proves strict contravariant composition

```text
pullback(g.comp f) = pullback(g) ≫ pullback(f).
```

It requires no inverse to that comparison. The theorem ending in `_congr`
uses equality of the actual continuous maps and proof irrelevance to
identify transformations with different equivariance and properness
witnesses.

`coefficientInvariantCohomologyNatTrans f hf hp q` is the chain
transformation whiskered by
`homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q`. Its source and target
are `L_Y` and `L_X` followed by the existing
`smoothGodementInvariantCompactCohomology` functors. The component theorem
identifies it with module homology of the constructed invariant chain map.
Its naturality is part of the constructed natural transformation. Identity
and strict composition follow by applying the homology functor to the
proved chain equations.

This is an internal construction. Its provenance is the full coefficient
spatial pullback in `SmoothDirectImage.Coefficients`, the proper coefficient
compact map in `SmoothGodement.CoefficientSpatial`, and the invariant spatial
map and comparison in `SmoothGodement.InvariantSpatial`. Whiskering,
extensionality, their proved identity and matching lax-composition equations,
and homology functoriality discharge the intrinsic obligations. No new
external-source assertion is introduced.

The result takes invariants degreewise before taking module homology.
It does not assert exactness of invariants or identify the result with
invariants of compact homology. Higher right-derived comparisons, Godement
acyclicity or resolution exactness, comparisons with the full equivariant
Godement route, compatibility of spatial maps with degree-zero section
isomorphisms, subgroup or quotient invariant maps, and analytic etale,
uniformization, Shimura and Harris specialization remain separate
obligations.
