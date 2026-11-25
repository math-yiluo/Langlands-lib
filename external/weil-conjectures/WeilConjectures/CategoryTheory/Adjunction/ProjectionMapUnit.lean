/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The projection map at the unit

Let `adj : F ⊣ G` be an adjunction between monoidal categories whose left adjoint `F` is oplax
monoidal with invertible unit comparison `η`. If the comparison `φ` of the right adjoint
projection map is the comonoidal structure `δ` of `F`, the projection map
`G M ⊗ 𝟙 ⟶ G (M ⊗ F 𝟙)` at the unit is an isomorphism
(`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_tensorUnit`): it is the
right unitor followed by `G` of the isomorphism `M ≅ M ⊗ F 𝟙` given by the unitor and `η⁻¹`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.OplaxMonoidal _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal] [IsIso (η F)]
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))

/-- The right adjoint projection map `G M ⊗ 𝟙 ⟶ G (M ⊗ F 𝟙)` at the unit is the right unitor
followed by `G` of the isomorphism `M ≅ M ⊗ F 𝟙`, when its comparison is `δ`. -/
lemma rightAdjointProjectionMap_app_app_tensorUnit (hφ : ∀ X Y, (φ.app X).app Y = δ F X Y)
    (M : C) :
    ((adj.rightAdjointProjectionMap φ).app M).app (𝟙_ D) =
      (ρ_ (G.obj M)).hom ≫ G.map ((ρ_ M).inv ≫ M ◁ inv (η F)) := by
  rw [rightAdjointProjectionMap_app_app, hφ]
  have h : δ F (G.obj M) (𝟙_ D) ≫ adj.counit.app M ▷ F.obj (𝟙_ D) =
      F.map (ρ_ (G.obj M)).hom ≫ adj.counit.app M ≫ (ρ_ M).inv ≫ M ◁ inv (η F) := by
    have hu := right_unitality F (G.obj M)
    calc δ F (G.obj M) (𝟙_ D) ≫ adj.counit.app M ▷ F.obj (𝟙_ D)
        = δ F (G.obj M) (𝟙_ D) ≫ F.obj (G.obj M) ◁ η F ≫ F.obj (G.obj M) ◁ inv (η F) ≫
            adj.counit.app M ▷ F.obj (𝟙_ D) := by
          rw [← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.hom_inv_id,
            MonoidalCategory.whiskerLeft_id, Category.id_comp]
      _ = F.map (ρ_ (G.obj M)).hom ≫ (ρ_ (F.obj (G.obj M))).inv ≫
            F.obj (G.obj M) ◁ inv (η F) ≫ adj.counit.app M ▷ F.obj (𝟙_ D) := by
          rw [hu]
          simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id,
            Category.id_comp]
      _ = _ := by
          rw [whisker_exchange, ← Category.assoc ((ρ_ _).inv),
            ← rightUnitor_inv_naturality, Category.assoc]
          rfl
  change adj.homEquiv _ _ (δ F (G.obj M) (𝟙_ D) ≫ adj.counit.app M ▷ F.obj (𝟙_ D)) = _
  rw [h]
  simp [homEquiv_unit]

/-- The right adjoint projection map `G M ⊗ 𝟙 ⟶ G (M ⊗ F 𝟙)` at the unit is an isomorphism, when
its comparison is the comonoidal structure `δ` of `F` and the unit comparison `η` of `F` is an
isomorphism. -/
lemma isIso_rightAdjointProjectionMap_app_app_tensorUnit (hφ : ∀ X Y, (φ.app X).app Y = δ F X Y)
    (M : C) : IsIso (((adj.rightAdjointProjectionMap φ).app M).app (𝟙_ D)) := by
  rw [rightAdjointProjectionMap_app_app_tensorUnit adj φ hφ]
  infer_instance

end CategoryTheory.Adjunction
