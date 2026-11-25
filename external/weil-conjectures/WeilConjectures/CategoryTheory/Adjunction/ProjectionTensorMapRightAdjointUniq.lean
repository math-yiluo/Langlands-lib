/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# The tensor map does not depend on the right adjoint

Let `adj : L ⊣ R` be an adjunction with a projection map `π M N : L M ⊗ N ⟶ L (M ⊗ F N)`, and
let `τ M N : R M ⊗ F N ⟶ R (M ⊗ N)` be its tensor map
(`CategoryTheory.Adjunction.projectionTensorMap`). Two right adjoints of `L` have the same tensor
maps through `CategoryTheory.Adjunction.rightAdjointUniq`
(`CategoryTheory.Adjunction.projectionTensorMap_rightAdjointUniq_hom`), so one tensor map is an
isomorphism if and only if the other one is
(`CategoryTheory.Adjunction.isIso_projectionTensorMap_iff_of_adjunction`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {L : C ⥤ D}
  (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]

section Uniq

variable {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L ⊣ R')

/-- **The tensor map does not depend on the right adjoint**: through the isomorphism
`ρ : R ≅ R'` of two right adjoints of `L`, the tensor maps of `L ⊣ R` and `L ⊣ R'` agree:

```
  R M ⊗ F N  ---τ--->  R (M ⊗ N)
     |                    |
  ρ_M ▷ F N           ρ_{M ⊗ N}
     ↓                    ↓
  R' M ⊗ F N ---τ'--> R' (M ⊗ N)
```
-/
@[reassoc]
lemma projectionTensorMap_rightAdjointUniq_hom
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (M N : D) :
    adj.projectionTensorMap π M N ≫ (rightAdjointUniq adj adj').hom.app (M ⊗ N) =
      (rightAdjointUniq adj adj').hom.app M ▷ F.obj N ≫ adj'.projectionTensorMap π M N := by
  apply ext_of_comp_counit (adj := adj')
  have h := hπ ((rightAdjointUniq adj adj').hom.app M) N
  rw [← cancel_epi (inv (π _ N)), ← cancel_mono (inv (π _ N))] at h
  simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
  rw [Functor.map_comp, Category.assoc, rightAdjointUniq_hom_app_counit,
    map_projectionTensorMap_comp_counit, Functor.map_comp, Category.assoc,
    map_projectionTensorMap_comp_counit, ← reassoc_of% h, ← comp_whiskerRight,
    rightAdjointUniq_hom_app_counit]

/-- The tensor map of `L ⊣ R` is an isomorphism if and only if that of `L ⊣ R'` is. -/
lemma isIso_projectionTensorMap_iff_of_adjunction
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (M N : D) :
    IsIso (adj.projectionTensorMap π M N) ↔ IsIso (adj'.projectionTensorMap π M N) := by
  have h := projectionTensorMap_rightAdjointUniq_hom π adj adj' hπ M N
  constructor
  · intro
    have : IsIso ((rightAdjointUniq adj adj').hom.app M ▷ F.obj N ≫
        adj'.projectionTensorMap π M N) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_left ((rightAdjointUniq adj adj').hom.app M ▷ F.obj N) _
  · intro
    have : IsIso (adj.projectionTensorMap π M N ≫
        (rightAdjointUniq adj adj').hom.app (M ⊗ N)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((rightAdjointUniq adj adj').hom.app (M ⊗ N))

end Uniq

end CategoryTheory.Adjunction
