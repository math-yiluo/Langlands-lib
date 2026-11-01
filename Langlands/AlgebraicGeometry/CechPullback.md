# Pullback of Čech cochains of structure sheaves along morphisms of schemes

Author: Worker 274.

This module pulls back ordered Čech cochains of the structure sheaf along a morphism of
schemes and proves that the pullback commutes with the Čech differential, with the products of
`Langlands.Cohomology.CechCup` and with composition. It also shows that two index maps for the
same morphism give pullbacks of a `1`-cocycle that differ by a coboundary. It is a helper for
the proof of `Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`. It
contains no `sorry` and no new axioms.

## Provenance

For a morphism `f : X ⟶ Y`, families of opens `U` of `Y` and `U'` of `X`, and an index map
`α` with `U' i ⊆ f⁻¹ U (α i)`, the map `c ↦ (σ ↦ f^♯ (c (α ∘ σ)))` is the composite of the
pullback of sections along `f` with the refinement map of The Stacks Project, Cohomology of
Sheaves, section "Refinements and Čech cohomology" (tag 09UY), `cohomology.tex` lines 2439–2480 of the registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`. The homotopy between the maps for two index
maps is the degree-one case of the homotopy `h` given there. The formalization is internal; its
names and form are a project choice.

## Definitions

All declarations are in namespace `Langlands.Cohomology.Cech`. Throughout,
`f : X ⟶ Y` is a morphism of schemes, `U : ι → Y.Opens`, `U' : ι' → X.Opens`, `α : ι' → ι` and
`hα : ∀ i, U' i ≤ f ⁻¹ᵁ U (α i)`.

- `pull f U U' α hα p : C (ab Y.presheaf) U p →+ C (ab X.presheaf) U' p` sends `c` to
  `σ ↦ f.appLE (inter U (α ∘ σ)) (inter U' σ) _ (c (α ∘ σ))`.
- `indexChange f U U' hα hα' z : C (ab X.presheaf) U' 0`, for a second index map `α'` with
  `hα'`, is `τ ↦ f^♯ (z (α' (τ 0), α (τ 0)))`.

## Results

- `mem_inter`: `x ∈ inter U σ ↔ ∀ a, x ∈ U (σ a)`.
- `inter_le_preimage hα σ`: `inter U' σ ≤ f ⁻¹ᵁ inter U (α ∘ σ)`.
- `pull_apply`, `res_appLE`, `appLE_res`, `appLE_congr_idx`, `face_pull`: computation rules.
- `d_pull`: `d (pull c) = pull (d c)`.
- `pull_prod`: `pull (prod n z) = prod n (fun k => pull (z k))`.
- `pull_one`: `pull (one Y.presheaf U) = one X.presheaf U'`.
- `pull_comp`: pulling back along `g : Y ⟶ Z` and then along `f` is pulling back along
  `f ≫ g` with the composite index map.
- `le_preimage_inter_two`: an open below `f⁻¹ U a` and `f⁻¹ U b` is below
  `f⁻¹ inter U ![a, b]`.
- `pull_sub_pull_eq_d`: for a `1`-cocycle `z`, the pullbacks of `z` for the index maps `α` and
  `α'` differ by `d (indexChange f U U' hα hα' z)`.
