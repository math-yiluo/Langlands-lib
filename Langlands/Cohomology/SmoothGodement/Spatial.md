# Proper spatial maps of separate smooth Godement compact cohomology

This module constructs proper spatial pullback on compact sections of the
separate smooth Godement complex, and on the already defined homology of that
complex in the smooth representation category. It proves component formulas,
naturality, and identity and lax-composition laws for these actual maps.

## Setting and actual chain map

The commutative coefficient ring `R`, topological group `G`, spaces, and
module carriers share universe `u`. Every space has a `G`-action with
continuous fixed translations and `HasStableNeighbourhoods`. The spatial
map `f : C(X, Y)` is continuous and equivariant by `hf`; `hp : IsProperMap f`
is required for compact pullback. A second map `g : C(Y, Z)` has the
corresponding proofs `hg` and `hq`.

The sheaves are the existing smooth module sheaves on the ordinary-open
transport category. Write `D_f` for `SmoothDirectImage.functor f hf`,
`K_X(F)` for the separate smooth Godement complex `Godement.smoothComplex
R G X F`, and `L_f(F)` for the constructed spatial chain map from
`Godement.SmoothSpatialComplex`. Write `C_X` for the degreewise full compact
sections functor `ProperSmoothCompactComplexes.compactComplex R G X
(ComplexShape.up ℕ)`. Its values are complexes in the existing abelian
category `Langlands.SmoothRep R G`.

The namespace is
`Langlands.Cohomology.SmoothGodementCohomology.Spatial`.
`compactNatTrans f hf hp` is the actual composite of compact sections of
`L_f` with the existing proper smooth compact-section transformation. Its
type is

```text
D_f ⋙ smoothGodementCompactComplex R G Y
  ⟶ smoothGodementCompactComplex R G X.
```

`compactMap f hf hp F` is its component. `compactMap_eq` records

```text
P_f(F) = C_Y.map(L_f(F)) ≫ properComplex_f(K_X(F)).
```

Both factors are genuine chain maps: the first comes from the constructed
higher smooth Godement map and the second from the actual proper pullback
of compact sections in each degree. This uses no additional exactness or
acyclicity premise.

`compactMap_f` gives the degree-`n` formula: apply
`smoothSheafCompactSections R G Y` to `L_f(F).f n`, then apply
`ProperSmoothCompactSections.natTrans f hf hp` at `K_X(F).X n`.
`compactMap_apply` shows the action on each original compact section `s`:
apply the global-section component of that constructed smooth sheaf map to
`s.val`, then forget the resulting smooth-image witness. Properness is what
makes this original section compactly supported on `X`.
`compactMap_f_zero` specializes the degree formula to the actual
`Godement.SmoothSpatial.zeroMap f hf F`.

## Naturality, identity and composition

`compactMap_naturality` is the naturality square for every smooth sheaf
morphism `a : F ⟶ F'`:

```text
compactComplex_Y.map(D_f.map(a)) ≫ P_f(F')
  = P_f(F) ≫ compactComplex_X.map(a),
```

where `compactComplex_X` in this formula means the composed functor
`smoothGodementCompactComplex R G X`.

Let `e : 𝟭 ≅ D_id` be the existing `SmoothDirectImage.idIso` and
`c_fg : D_f ⋙ D_g ⟶ D_(g.comp f)` be the existing
`SmoothDirectImage.compMap f hf g hg`. The equations are

```text
compactComplex_X.map(e.hom(F)) ≫ P_id(F) = 𝟙,

compactComplex_Z.map(c_fg(F)) ≫ P_(g.comp f)(F)
  = P_g(D_f(F)) ≫ P_f(F).
```

These are `compactMap_id` and `compactMap_comp`. The identity proof applies
compact sections to the smooth Godement chain identity law and then uses
`properComplex_id`. The composition proof applies compact sections to the
proved chain law, combines the proper pullbacks using `properComplex_comp`,
and moves the intermediate chain map through the proper transformation by
its naturality. The lax comparison is retained explicitly and is not assumed
invertible.

## Actual cohomology maps

`cohomologyNatTrans f hf hp q` applies the homology functor in
`Langlands.SmoothRep R G` to `compactNatTrans`. Its type is

```text
D_f ⋙ smoothGodementCompactCohomology R G Y q
  ⟶ smoothGodementCompactCohomology R G X q.
```

`cohomologyMap` is the component, and `cohomologyMap_eq` identifies it with
the actual homology of `compactMap`. These reuse the already defined
`smoothGodementCompactCohomology` objects, rather than introducing new
cohomology values or a supplied comparison map.

`cohomologyMap_naturality`, `cohomologyMap_id` and `cohomologyMap_comp`
give the same naturality, identity and lax-composition equations in every
degree `q`. The proofs apply homology to the proved chain equations and use
functoriality. The naturality, identity and composition laws, at both levels,
also have reassociated forms through their `reassoc` attributes.

## Provenance and remaining scope

This is internal construction from the existing `SmoothGodementCohomology`,
`Godement.SmoothSpatialComplex`, `ProperSmoothCompactComplexes`, and
`ProperSmoothCompactSections` modules. It composes their actual functors,
chain maps and support-preserving maps, and proves the remaining equations
by their naturality and composition laws. It makes no new external-source
assertion.

The objects are compact cohomology through the separate smooth Godement
complex. This module does not identify them with right derived compact
sections, compare them with smooth sections of the full equivariant Godement
complex, or assert exactness, acyclicity, compatibility with the degree-zero
cohomology identification, support-forgetting comparisons, invariant
cohomology maps, or analytic, etale or Shimura realizations. No local
compactness, Hausdorff condition, right exactness of smooth direct image or
invertibility of its lax comparison is assumed.
