# Uniform vanishing of higher fibre cohomology of large twists

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistUniformVanishing` (namespace
`Langlands.AlgebraicGeometry.Modules.FibreTwist`) proves clause 1 of
`ProjectiveFibreTwistCohomologyStatement`, together with helpers shared with the other clauses.

## Twists

For modules `𝓛`, `F` on a scheme (FLT tensor products), `twist 𝓛 F n` is the twist of the statement.

- `twistTensorPowIso`: `twist 𝓛 F n ≅ F ⊗ 𝓛.tensorPow n` (FLT tensor power), by the right unitor
  and associators.
- `pullbackTwistIso`: pullback commutes with twisting (FLT `pullbackTensorObjIso`).
- `isInvertible_twist`: twists of invertible modules are invertible.

## Fibre models

- `homologyBaseChangeIdIso`: a complex of modules and its base change along the identity have
  isomorphic homology (Mathlib's `ModuleCat.extendScalarsId`).
- `exists_fibreModel_sections`: the fibre model of the proof of
  `ProperFlatFibreCohomologySemicontinuityStatement` (`FibreSemicontinuity.exists_perfectModel`,
  module `ProperFlatFibreCohomologySemicontinuityProof`), with one more property. Let `g : Y ⟶ T`
  be proper and flat, `F` invertible, and `V` an affine open with noetherian `Γ(T, V)`. There is a
  strictly perfect complex `K` of `Γ(T, V)`-modules such that `Hⁿ(Y_t, F_t) ≅ Hⁿ(K ⊗ κ(t))` for
  `t ∈ V` (with no negative homology), and moreover `Hⁿ(K) ≅ Hⁿ(g⁻¹(V), F)` for `n ≥ 0`. The last
  isomorphism uses the model's base change along the identity of `Γ(T, V)` and the cartesian
  square with identity sides (Library `nonempty_relativeCohomology_iso_chosenPullback`,
  `Scheme.Modules.pullbackId`).
- `isZero_fibreCohomology_of_model`: if such a model has `Hⁿ(K) = 0` for `n > 0`, then
  `Hᵖ(Y_t, F_t) = 0` for all `t ∈ V` and `p > 0`. Mumford's Corollary 3 in algebraic form
  (`homologyDim_eq_zero_of_isZero_homology`, module `Langlands.Cohomology.PerfectComplexVanishing`)
  gives `dim Hᵖ(K ⊗ κ(t)) = 0`, and these spaces are finite-dimensional.

## Clause 1 (`uniformVanishing`)

Let `A` be noetherian, `f : X ⟶ Spec A` proper and flat, `𝓛X` invertible with a presentation `𝔓`
whose morphism to `ℙᴺ_A` is a closed immersion, `T` locally noetherian, `s : T ⟶ Spec A` and `F`
invertible on `X_T`. For `t₀ ∈ T`, there are a neighbourhood `V` and `n₀` with
`Hᵖ(X_{t'}, F(n)_{t'}) = 0` for `t' ∈ V`, `n ≥ n₀`, `p > 0`.

1. Take an affine open `V ∋ t₀` with noetherian ring `R = Γ(T, V)`, the restriction
   `g_V : X_T|_V ⟶ Spec R` (Library `affineRestrict`) and the ring map `A → R` with
   `Spec R ⟶ Spec A` equal to `V ⟶ T ⟶ Spec A` (Mathlib `Spec.preimage`). Pasting
   `isPullback_affineRestrict` with the chosen pullback square of `f` along `s` gives a cartesian
   square over `Spec R ⟶ Spec A`. The FLT theorem `ProjPresentation.exists_baseChange_of_isPullback`
   then gives a presentation of the pullback `L` of `𝓛X` to `X_T|_V`. Its morphism to `ℙᴺ_R` is a
   closed immersion, as a base change of one.
2. Relative Serre vanishing (`CechBridge.exists_isZero_relativeCohomology_tensor_tensorPow`,
   module `RelativeSerreVanishingInvertible`) gives `n₀` with
   `Hⁱ(X_T|_V, F|_V ⊗ L^{⊗ n}) = 0` for `n ≥ n₀`, `i > 0`.
3. For `n ≥ n₀`, apply `exists_fibreModel_sections` to `F(n)`. The restriction of `F(n)` to
   `X_T|_V` is `F|_V ⊗ L^{⊗ n}` (`pullbackTwistIso`, `twistTensorPowIso`). So the model has no
   homology in positive degrees, and `isZero_fibreCohomology_of_model` gives the vanishing on all
   fibres over `V`.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
