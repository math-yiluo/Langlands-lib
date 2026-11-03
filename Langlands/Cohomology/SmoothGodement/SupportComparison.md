# Global sections and support forgetting for the separate smooth Godement complex

This module constructs spatial maps on all global sections of the separate
smooth Godement complex. It compares the proper compact spatial maps with
these maps by actual support-forgetting inclusions, both on complexes and
on their homology.

## Setting and global objects

The commutative coefficient ring `R`, topological group `G`, spaces and module
carriers share universe `u`. Each space has a `G`-action with continuous
fixed translations and `HasStableNeighbourhoods`. The sheaves are the existing
smooth module sheaves on the transport category of ordinary open sets.
A spatial map `f : C(X, Y)` is continuous and equivariant by `hf`. Only compact
pullback requires `hp : IsProperMap f`. No Hausdorff or local compactness
hypothesis is used.

Write `K_X` for `Godement.smoothComplexFunctor R G X`, `D_f` for
`SmoothDirectImage.functor f hf`, `U` for `Langlands.SmoothRep.toRep`,
`C_X` for `ProperSmoothCompactComplexes.compactComplex`, and `A_X` for
`ProperSmoothCompactComplexes.globalComplex`, with shape `ComplexShape.up ℕ`.
Write `L_f(F) : K_Y(D_f(F)) ⟶ D_f,complex(K_X(F))` for the previously
constructed separate smooth Godement spatial chain map.

In namespace `Langlands.Cohomology.SmoothGodementCohomology`,
`smoothGodementGlobalComplex R G X` is `K_X ⋙ A_X`. It takes all global
sections of the original underlying sheaves in every degree, with the
original group actions and differentials. Its values are cochain complexes
in algebraic representations `Rep R G`; smoothness of every global section
is not imposed. `smoothGodementGlobalCohomology R G X q` is its homology in
that abelian category.

`forgetSupportComplex` has type

```text
smoothGodementCompactComplex X ⋙ U.mapHomologicalComplex (up ℕ)
  ⟶ smoothGodementGlobalComplex X.
```

It specializes `ProperSmoothCompactComplexes.forgetSupportComplex` to `K_X`.
`forgetSupportComplex_apply` proves that its degreewise value on an original
compact section `s` is exactly `s.val`.

`forgetSupport q` has type

```text
smoothGodementCompactCohomology X q ⋙ U
  ⟶ smoothGodementGlobalCohomology X q.
```

It specializes the existing `forgetSupportHomology`. By `forgetSupport_app`,
its component is the inverse of the proved exact-inclusion homology
comparison, followed by ordinary homology of `forgetSupportComplex`.
Thus it uses the existing proved finite-limit and finite-colimit preservation
of `U`, without assuming commutation of an arbitrary functor with homology.

## Actual global spatial maps

In the nested namespace `Spatial`, `globalNatTrans f hf` has type

```text
D_f ⋙ smoothGodementGlobalComplex Y ⟶ smoothGodementGlobalComplex X.
```

`globalMap f hf F` is its component. `globalMap_eq` identifies it with

```text
A_Y.map(L_f(F)) ≫ globalComplexMap_f(K_X(F)).
```

The second factor applies the actual smooth-image inclusion into ordinary
direct image, then the ordinary global-section identification. Both factors
are already constructed chain maps. Properness is unnecessary.

`globalMap_apply` gives the degreewise formula on each original global
section: apply the global-section component of `L_f(F).f n`, then take the
underlying section of its smooth-direct-image value. The zero-degree formula
`globalMap_apply_zero` uses precisely `Godement.SmoothSpatial.zeroMap`.
`globalMap_naturality` covers every original smooth sheaf morphism.

Let `e : 𝟭 ≅ D_id` be `SmoothDirectImage.idIso` and
`c_fg : D_f ⋙ D_g ⟶ D_(g.comp f)` be `SmoothDirectImage.compMap`.
The proved equations are

```text
globalComplex_X.map(e.hom(F)) ≫ globalMap_id(F) = 𝟙,

globalComplex_Z.map(c_fg(F)) ≫ globalMap_(g.comp f)(F)
  = globalMap_g(D_f(F)) ≫ globalMap_f(F).
```

Here `globalComplex_X` means `smoothGodementGlobalComplex R G X`.
These are `globalMap_id` and `globalMap_comp`. They retain the actual
identity and lax-composition comparisons. No inverse of `c_fg` is assumed.
The module first proves `ProperSmoothCompactComplexes.globalComplexMap_id`
and `globalComplexMap_comp` on arbitrary smooth sheaf complexes of any shape
`c : ComplexShape I`, with `I : Type t`. Their proofs compare original
sections degreewise. Applying `A_X` to the previously proved smooth Godement
chain laws, then these global-section laws and naturality, proves the
specialized equations.

`globalCohomologyNatTrans f hf q` is ordinary homology of `globalNatTrans`;
`globalCohomologyMap` is its component. `globalCohomologyMap_eq` records that
factorization. Its naturality, identity and lax-composition equations are
`globalCohomologyMap_naturality`, `globalCohomologyMap_id` and
`globalCohomologyMap_comp`, proved by homology functoriality.

## Support-forgetting spatial comparisons

For proper `f`, `compactMap_forgetSupport` proves the actual chain square

```text
U_complex.map(compactMap_f(F)) ≫ forgetSupportComplex_X(F)
  = forgetSupportComplex_Y(D_f(F)) ≫ globalMap_f(F).
```

The compact map is the existing one from `SmoothGodement.Spatial`. The proof
uses the naturality of the support-forgetting transformation at `L_f(F)`
and the existing proper chain inclusion triangle.

`cohomologyMap_forgetSupport` proves the corresponding square

```text
U.map(cohomologyMap_f(F,q)) ≫ forgetSupport_X(F,q)
  = forgetSupport_Y(D_f(F),q) ≫ globalCohomologyMap_f(F,q).
```

It follows by naturality of the inverse exact-inclusion homology isomorphism
and ordinary homology of the proved chain square. Naturality, identity,
composition and spatial support squares also have reassociated forms.

## Provenance and remaining scope

This is internal construction from `SmoothGodement.Spatial`,
`Godement.SmoothSpatialComplex`, `ProperSmoothCompactComplexes` and their
actual section functors. The new global objects are obtained by applying
those functors to the existing resolution; the maps are explicit composites.
The intrinsic laws follow from original-section extensionality, proved
spatial chain laws, naturality and functoriality. No new external-source
assertion is made.

The cohomology objects here are homology of the separate smooth Godement
section complexes. This module does not identify them with right derived
sections, establish exactness or acyclicity of a resolution, identify them
with smooth sections of the full equivariant Godement complex, or construct
invariant spatial maps. Compatibility with the existing degree-zero
cohomology isomorphisms and analytic, etale or Shimura realization remain
separate obligations.
