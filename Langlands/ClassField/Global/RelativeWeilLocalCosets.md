# Double cosets of a local map and the places of an intermediate field

Lean module: `Langlands.ClassField.Global.RelativeWeilLocalCosets`.

This module supplies the double-coset data that Mackey's formula needs for the local
restriction formula `Langlands.ClassField.Global.RelativeWeilGroup.LocalInducedRestrictionStatement`.
It is derived infrastructure; no theorem of the type `LocalInducedRestrictionStatement` is
proved here.

## Provenance

The mathematical content is the double-coset bijection in Tate, *Number theoretic
background* (1979), Example (2.3.5), printed p.12 (literature ID
`tate-1979-number-theoretic-background`): if `w₀` is one place of `E` over `v`, then
`σ ↦ σ w₀` puts the double cosets `W_E \ W_F / W_{F_v}` in bijection with the places of `E`
over `v`, and the intersection of `W_E` with a conjugate of `W_{F_v}` is identified with
`W_{E_w}`. Tate states this for absolute Weil groups and gives no proof. This module
proves the relative version for `F ⊆ K ⊆ E` with `E / F` Galois (Tate's `E` is our `K`):
for a finite place `z` of `F`, a place `w` of `E` above `z` and a homomorphism
`ι : W_{F_z} → W_{E/F}` satisfying condition 2 of `IsLocalRelativeWeilMap`, the double
cosets `W_{E/K} \ W_{E/F} / ι(W_{F_z})` are indexed by the places `u` of `K` above `z`, and
the conjugate of `ι` by a representative of `u`, restricted to `W_{K_u}`, lands in
`W_{E/K}`. The proof uses embeddings into the algebraic closure
`\bar{F_z} = AlgebraicClosure (z.adicCompletion F)` rather than decomposition groups.

## Local part (section `Places`)

For a place `u : FinitePlacesAbove K z`:

- `placeEmbedding z u : K →+* \bar{F_z}` is `k ↦ completionClosureEmbedding z u (k)`, the
  embedding `K → K_u → \bar{F_z}` along which the published `completionWeilMap z u` is
  formed. `placeClosureAlgHom z u` is `completionClosureEmbedding z u` as a homomorphism
  of `F_z`-algebras; `placeClosureAlgHom_algebraMap` says it extends `placeEmbedding z u`,
  and `placeClosureAlgHom_completionMap` says it is `F_z`-linear for the published
  `FiniteExtension.completionMap z u`.
- `placeEmbedding_fixed_iff`: an element `τ` of `G_{F_z}` fixes `placeEmbedding z u`
  pointwise iff `τ` is in the range of `Weil.Local.extensionGaloisMap` for `K_u / F_z`.
  The proof uses the published `extensionGaloisMap_range` (the range is the fixing
  subgroup of the image of `K_u`) and `subalgebra_eq_top_of_algebraMap_mem` (the image
  of `K` generates `K_u` over `F_z`), applied to the equalizer of `τ ∘ j_u` and `j_u`.
- `eq_of_placeEmbedding_eq`: if `τ ∘ placeEmbedding z u = placeEmbedding z u'` for some
  `τ ∈ G_{F_z}`, then `u = u'`. Both sides give `F_z`-algebra maps
  `F_z ⊗_F K → \bar{F_z}` through `finiteTensorMap z` that agree on pure tensors, hence
  are equal (`Algebra.TensorProduct.ext'`). An element mapping to the idempotent
  `Pi.single u 1` (surjectivity, `finiteTensorMap_surjective`) is sent to `1` by the
  first and to `0` by the second if `u ≠ u'`.
- `exists_placeEmbedding`: every ring map `ε : K → \bar{F_z}` that is `F`-linear is
  `τ ∘ placeEmbedding z u` for some `u` and `τ ∈ G_{F_z}`. The proof extends `ε` to an
  `F_z`-algebra map `F_z ⊗_F K → \bar{F_z}`, transports it along the bijection
  `finiteTensorMap z` (bijective by `finiteTensorMap_bijective_of_local_degree_bounds`
  and `completedLocalDegreeLowerBound`), finds an idempotent `Pi.single u 1` with image
  `1`, obtains an `F_z`-algebra map `K_u → \bar{F_z}`, and lifts it to an automorphism of
  the normal extension `\bar{F_z}` (`AlgHom.liftNormal`, `AlgHom.normal_bijective`).
- `exists_dense_placeEmbedding`: for any map `f : X → G_{F_z}` with dense range and any
  `τ ∈ G_{F_z}`, some `f x` agrees with `τ` on the image of `placeEmbedding z u`. The set
  of automorphisms agreeing with `τ` there is the translate `τ · R` of the range `R` of
  `extensionGaloisMap` (by `placeEmbedding_fixed_iff`), which is open by
  `extensionGaloisMap_range_isOpen`.
- `exists_localProjection_placeEmbedding`: the case `f = localProjection` of the previous
  item, using the published `localProjection_denseRange`: every `τ ∈ G_{F_z}` agrees on
  the image of `placeEmbedding z u` with `localProjection ℓ` for some `ℓ ∈ W_{F_z}`.
- `exists_eq_comp_completionClosureEmbedding`: every ring map `κ : K_u → \bar{F_z}` that
  is `F_z`-linear is `τ ∘ completionClosureEmbedding z u` for some `τ ∈ G_{F_z}`
  (again by `AlgHom.liftNormal`).

## Global part (section `Cosets`)

In this section `Gal(E/F)` carries the Library's discrete topology `relativeGaloisTopology`
(a local instance), as in `RelativeWeilLocalRestrictionStatement`.

- `closurePlaceEmbedding z w : E →+* \bar{F_z}` is `E → E_w → \bar{F_z}`, the embedding in
  condition 2 of `IsLocalRelativeWeilMap`; `closurePlaceEmbedding_algebraMap` says it is
  `F`-linear.
- `cosetEmbedding c K z w g : K →+* \bar{F_z}` is `k ↦ j_w((projection g)⁻¹ k)`
  (`cosetEmbedding_apply`); it is `F`-linear (`cosetEmbedding_algebraMap`).
- `aut_inv_apply_apply`, `aut_apply_inv_apply` and `absoluteGalois_inv_apply_apply` are the
  cancellation rules `σ⁻¹ (σ x) = x` and `σ (σ⁻¹ x) = x` for `Gal(E/F)` and `G_{F_z}`.
- `mem_range_restrictScalarsHom_iff`: an `F`-automorphism of `E` comes from `Gal(E/K)` iff
  it fixes `K`.
- `mem_range_restrictionInclusion_iff`: `g' * g⁻¹` is in the image of `W_{E/K}` iff
  `cosetEmbedding g = cosetEmbedding g'`. It uses the published `range_restrictionInclusion`
  and `mem_range_restrictScalarsHom_iff`.
- `exists_cosetEmbedding_eq`: every `placeEmbedding z u` is a coset embedding. The
  embedding is extended to `E` (`IsAlgClosed.lift`), written as `j_w ∘ τ` with `τ ∈ Gal(E/F)`
  (`AlgHom.restrictNormal'`), and `τ⁻¹` is lifted along `projection_surjective`.
- For a homomorphism `ι : W_{F_z} →* W_{E/F}` with
  `j_w(projection (ι g) x) = localProjection g (j_w x)` (condition 2 of
  `IsLocalRelativeWeilMap`):
  - `cosetEmbedding_mul`: `cosetEmbedding (g * ι ℓ) = localProjection ℓ⁻¹ ∘ cosetEmbedding g`;
  - `conj_mem_range_restrictionInclusion_iff`: if `cosetEmbedding x = placeEmbedding z u`,
    then `x * ι ℓ * x⁻¹` is in the image of `W_{E/K}` iff `ℓ` is in the range of
    `completionWeilMap z u` (uses `placeEmbedding_fixed_iff` and the published
    `extensionWeilMap_range`);
  - `place_eq_of_mul_eq`: `j m * (x u * ι ℓ) = j m' * (x u' * ι ℓ')` implies `u = u'`;
  - `exists_eq_mul`: every `g` is `j m * (x u * ι ℓ)` for some `m`, `u`, `ℓ`.
  Here `j = restrictionInclusion c F E K h`, and `x u` is any family with
  `cosetEmbedding (x u) = placeEmbedding z u`, for example the representatives below.
- `placeRepresentative c K z w u` is a chosen `g` with `cosetEmbedding g = placeEmbedding z u`
  (`cosetEmbedding_placeRepresentative`).
- `localPlaceMap c K z w h ι hι u : W_{K_u} →ₜ* W_{E/K}`, for a continuous `ι`, is
  `n ↦ j⁻¹(x_u · ι(completionWeilMap z u n) · x_u⁻¹)` with `x_u = placeRepresentative c K z w u`,
  read back in `W_{E/K}` through `InductionAlong.rangeInverse`; the conjugate lies in the
  image of `j` by `conj_mem_range_restrictionInclusion_iff`. It is continuous because
  `restrictionInclusion` is an embedding. `restrictionInclusion_localPlaceMap` records the
  defining identity `j (localPlaceMap … u n) = x_u * ι (completionWeilMap z u n) * x_u⁻¹`.
