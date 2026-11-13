# Generator fields at the distinguished place of a global realization

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. Deligne's global argument
(1973, proof of Lemma 4.12) realizes a finite Galois extension `K / F` of p-adic fields as the
completion at a place `w` over `v` of a Galois extension `K' / k` of number fields, through the
published statement `Langlands.Global.TotallyRealGaloisRealizationStatement`. Its data are ring
isomorphisms `φ : k_v ≃ F` and `ψ : K'_w ≃ K`, a group isomorphism
`θ : Gal(K'/k) ≃ Gal(K/F)`, the compatibility `ψ ∘ (k → K'_w) = (F → K) ∘ φ ∘ (k → k_v)` on `k`
(called `hcomp` below) and `θ σ (ψ x) = ψ (σ x)` for `x ∈ K'` (called `hθ`).

This unit shows that, for an intermediate field `L` of `K / F` (a finite intermediate field of
the common closure contained in `K`), the realization identifies the completion of the global
subfield `𝕃 = K'^{θ⁻¹ Gal(K/L)}` at a place `u` between `v` and `w` with `L`, as `ℚ_p`-algebras and
compatibly with `F`. The facts are the Galois correspondence together with continuity and density
of global fields in their completions; they are standard and have no separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. The field `K` is an `Extension F` (a
finite intermediate field of the fixed algebraic closure of `F`), normal over `F`, and topologies
on fields of the closure are the canonical ones of their `asPadicField` repackagings.

## Galois correspondence

For fields `k ⊆ K'`, `F ⊆ K`, a group isomorphism `θ : Gal(K'/k) ≃ Gal(K/F)`, a ring homomorphism
`j : K' → K` with `θ σ (j x) = j (σ x)`, and a subgroup `H ≤ Gal(K/F)`:

- `map_mem_fixedField_comap`: `j` maps the fixed field of `θ⁻¹ H` into the fixed field of `H`
  (every element of `H` is `θ σ` with `σ ∈ θ⁻¹ H`).
- `fixedField_le_of_map_mem`: if both extensions are finite, `K / F` is Galois, and an
  intermediate field `M` of `K / F` contains `j` of the fixed field of `θ⁻¹ H`, then the fixed field
  of `H` is contained in `M`. Proof: an element `θ σ` of the fixing group of `M` fixes `j` of the
  fixed field of `θ⁻¹ H` and `j` is injective, so `σ` fixes that fixed field; by Mathlib's Galois
  correspondence (`fixingSubgroup_fixedField`) `σ ∈ θ⁻¹ H`. Hence `Fix(M) ≤ H`, and
  `fixedField H ≤ fixedField Fix(M) = M` (`IsGalois.fixedField_fixingSubgroup`).

For `L ⊆ K` inside the common closure, with `K / F` normal:

- `mem_galoisImage_iff`: an element of `Gal(K/F)` lies in the image `galoisImage F K L` of the
  Weil group of `L` exactly when it fixes every element of `K` lying in `L`. Proof: write it as the
  restriction of a Weil element (`galoisRestriction_surjective`) and use the published
  `galoisRestriction_mem_galoisImage_iff`.
- `fixedField_galoisImage`: the fixed field of `galoisImage F K L` in `K` is `L`, viewed as an
  intermediate field of `K / F` (`IntermediateField.restrict`). Proof: by the previous item the
  Galois image is the fixing subgroup of that intermediate field; `K / F` is Galois in
  characteristic zero.

## Topology

- `realizationField_t2Space`: the canonical topology of a field of the closure is Hausdorff.
- `continuous_algHom_field`: an `F`-algebra map `K → L` between fields of the closure is
  continuous. Proof: it is `ℚ_p`-linear, and both topologies are the `ℚ_p`-module topologies.
- `continuous_algebraMap_field`: the structure map `F → K` is continuous, by the same argument.
- `continuous_algebraMap_padicField`, `padicField_t2Space`: for a p-adic field `F` with its
  canonical topology, the structure map `ℚ_p → F` is continuous and `F` is Hausdorff.

## Completions

Here `k ⊆ K'` are number fields (in `Type`), `v` a finite place of `k`, `w` one of `K'` over `v`,
and `completionMap` the completion embedding of a tower of places.

- `realization_completionMap`: for continuous `φ` and `ψ` satisfying `hcomp`, the realization
  restricts to `φ` on the completion: `ψ (completionMap v w x) = φ x` in `K` for all `x ∈ k_v`.
  Proof: both sides are continuous in `x` and agree on the dense image of `k`.
- `realization_fixes_completion`: if `𝕃 ⊆ K'` is a number field, `u` the place of `𝕃` under `w`,
  and an `F`-automorphism `τ` of `K` fixes `ψ` of the image of `𝕃`, then `τ` fixes `ψ` of the
  image of the completion `𝕃_u`. Proof: continuity of `τ` and `ψ`, and density.
- `realizationSubfield K θ L` is the fixed field in `K'` of `θ⁻¹ (galoisImage F K L)`, the global
  field `𝕃` attached to `L`.
- `realization_completion_mem`: for `L ⊆ K` and `hθ`, `ψ` maps the completion of `𝕃` at a place
  `u` under `w` into `L`. Proof: by `map_mem_fixedField_comap` and
  `realization_fixes_completion`, the image is fixed by `galoisImage F K L`, whose fixed field is
  `L` (`fixedField_galoisImage`).
- `realizationCompletionHom`: the resulting ring homomorphism `𝕃_u → L`; on underlying elements
  of the closure it is `y ↦ ψ (completionMap u w y)` (`realizationCompletionHom_apply`).
- `realizationCompletionHom_surjective`: if moreover `φ`, `ψ` are continuous, `hcomp` holds, and
  `u` lies over `v`, the homomorphism is onto `L`. Proof: its image in `K` is a subfield, and it
  contains `F` because `ψ (completionMap u w (completionMap v u (φ⁻¹ a))) = a` by the tower law
  for completion maps (`CompletionTower.completionMap_comp`) and `realization_completionMap`. So
  the image is an intermediate field `M` of `K / F` containing `ψ` of `𝕃`;
  `fixedField_le_of_map_mem` gives `L = fixedField (galoisImage F K L) ≤ M`.

## The generator-field isomorphism

Now `F : PadicField (residuePrime v)`, so that the canonical p-adic packages of completions over
`v` have the same prime (after `residuePrime_eq_of_ringEquiv` this is achieved by substitution).
`towerPadicField v u` is the published `ℚ_p`-package of `𝕃_u`, and `L.asPadicField` that of `L`.

- `realization_padicMap`: a continuous `φ : k_v ≃ F` fixes `ℚ_p`:
  `φ (padicMap v a) = algebraMap ℚ_p F a`, by `ringHom_algebraMap_of_continuous`.
- `realizationBaseAlgHom v u φ hφ'`: for continuous `φ⁻¹`, the `ℚ_p`-algebra map
  `F → k_v → 𝕃_u`, the composite of `algHomOfContinuous` applied to `φ⁻¹` with the published
  `RelativeWeilGroup.completionPadicAlgHom v u`. As a function it is
  `a ↦ completionMap v u (φ⁻¹ a)` (`realizationBaseAlgHom_apply`).
- `realizationGeneratorEquiv`: under the hypotheses of `realizationCompletionHom_surjective`, the
  bijective ring homomorphism `realizationCompletionHom` as an isomorphism of `ℚ_p`-algebras
  `𝕃_u ≃ L`. Compatibility with `ℚ_p`: the structure map of `𝕃_u` is
  `completionMap v u ∘ padicMap v` (`completionMap_comp_padicMap`); then the tower law,
  `realization_completionMap` and `realization_padicMap` reduce both sides to the image of
  `algebraMap ℚ_p F a` in the closure. `realizationGeneratorEquiv_apply` records the underlying
  function `y ↦ ψ (completionMap u w y)`.
- `realizationGeneratorEquiv_base`: the isomorphism lies over `F`: for `a ∈ F`, the image of
  `realizationBaseAlgHom v u φ hφ' a` is `a` in the closure. This is the hypothesis `hσ` of
  `generatorValue_eq_epsilon_of_algEquiv`.
