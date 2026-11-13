# Finite intermediate fields along an isomorphism of p-adic fields

Worker 5130, Task 5230. Internal derived infrastructure; no external source.

Fix `g : F ≃ₐ[ℚ_p] E` between p-adic fields over the same prime, possibly in
different universes. `closureEquiv F E g` is the Library's chosen extension
`extensionClosureEquiv F E g.toAlgHom : F̄ ≃+* Ē` of `g` to the specified algebraic
closures; `closureEquiv_algebraMap` and `closureEquiv_symm_algebraMap` say that it
extends `g` and `g⁻¹`.

* `mapField F E g L` is the image `σ(L)` of a finite intermediate field `L` of `F̄`
  under the closure isomorphism, as an intermediate field of `Ē` over `E`. It is
  finite-dimensional over `E` because `mapFieldSemilinear` is a surjective
  `g`-semilinear map from `L`. `mapExtension` packages it as an `Extension E`.
  `mem_mapField_iff` describes membership; `mapExtension_mono` gives monotonicity;
  `mapField_bot` says the bottom field goes to the bottom field.
* `mapFieldRingEquiv L : L ≃+* σ(L)` is the restriction of the closure isomorphism.
  `padicAlgEquivOfRingEquiv` turns a ring isomorphism of p-adic fields that commutes
  with the maps from `ℚ_p` into a `ℚ_p`-algebra isomorphism. `fieldEquiv L` is
  `mapFieldRingEquiv L` regarded as an algebra isomorphism
  `L.asPadicField ≃ₐ[ℚ_p] σ(L).asPadicField`. Its type is inferred, so that it
  carries the p-adic field instances of `asPadicField`. These differ from the
  intermediate-field algebra instances, so the AlgEquiv API (for example `.symm`)
  is used through `mapFieldRingEquiv` instead.
* `weilEquiv F E g` is the Library's `extensionWeilEquiv F E g : W_E ≃ₜ* W_F`.
  `galoisMap_mem_fixingSubgroup_iff` and `weilEquiv_mem_iff` show that it carries the
  Weil subgroup of `σ(L)` onto that of `L`. `subgroupWeilEquiv L : W_E(σ(L)) ≃ₜ* W_F(L)`
  is the restriction, and `subgroupWeilEquiv_coe` and `subgroupWeilEquiv_symm_coe`
  give its values.
