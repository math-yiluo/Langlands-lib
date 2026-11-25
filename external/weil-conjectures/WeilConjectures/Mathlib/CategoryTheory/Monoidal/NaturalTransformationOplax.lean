/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Monoidal natural transformations: comonoidal criteria

This file collects criteria for a natural transformation between monoidal functors to be
monoidal (`NatTrans.IsMonoidal`).

* For strong monoidal functors, it suffices that the transformation is compatible with the
  comonoidal structures `η` and `δ` (`CategoryTheory.NatTrans.IsMonoidal.of_η_δ`), and, for an
  isomorphism, with `δ` alone (`CategoryTheory.NatTrans.IsMonoidal.of_isIso_of_δ`).
* A transformation `τ` is monoidal as soon as `τ ◫ H` is, for a faithful strong monoidal
  functor `H` (`CategoryTheory.NatTrans.IsMonoidal.of_whiskerRight`).
* Replacing the right adjoint of a monoidal adjunction by a monoidally isomorphic functor gives
  a monoidal adjunction (`CategoryTheory.Adjunction.isMonoidal_ofNatIsoRight`).
* The comparison isomorphism `Adjunction.leftAdjointUniq` between two left adjoints of a lax
  monoidal functor, through monoidal adjunctions, is compatible with the oplax monoidal
  structures (`CategoryTheory.Adjunction.leftAdjointUniq_hom_app_unit_comp_η`,
  `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_tensor_comp_δ`), hence is monoidal for
  strong monoidal left adjoints (`CategoryTheory.Adjunction.isMonoidal_leftAdjointUniq_hom`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

namespace NatTrans

/-- A natural transformation between strong monoidal functors which is compatible with the
comonoidal structures `η` and `δ` is monoidal. -/
lemma IsMonoidal.of_η_δ {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G)
    (hη : τ.app (𝟙_ C) ≫ η G = η F)
    (hδ : ∀ X Y : C, τ.app (X ⊗ Y) ≫ δ G X Y = δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y)) :
    IsMonoidal τ where
  unit := by
    rw [← cancel_mono (η G), Category.assoc, hη, Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  tensor X Y := by
    rw [← cancel_mono (δ G X Y), Category.assoc, hδ, Functor.Monoidal.μ_δ_assoc,
      Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

/-- A natural isomorphism between strong monoidal functors which is compatible with the
comonoidal structures `δ` is monoidal: the compatibility with the unit comparisons is
automatic. -/
lemma IsMonoidal.of_isIso_of_δ {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G) [IsIso τ]
    (hδ : ∀ X Y : C, τ.app (X ⊗ Y) ≫ δ G X Y = δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y)) :
    IsMonoidal τ := by
  have hμ (X Y : C) : μ F X Y ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y := by
    rw [← cancel_mono (δ G X Y), Category.assoc, hδ, Functor.Monoidal.μ_δ_assoc,
      Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  have key : (ε F ≫ τ.app (𝟙_ C)) ▷ G.obj (𝟙_ C) = ε G ▷ G.obj (𝟙_ C) := by
    rw [← cancel_epi (𝟙_ D ◁ τ.app (𝟙_ C)),
      ← cancel_mono (μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom)]
    simp only [Category.assoc]
    rw [← Functor.LaxMonoidal.left_unitality, comp_whiskerRight_assoc, whisker_exchange_assoc,
      ← tensorHom_def'_assoc, ← reassoc_of% (hμ (𝟙_ C) (𝟙_ C)), ← τ.naturality,
      ← Functor.LaxMonoidal.left_unitality_assoc, leftUnitor_naturality]
  have e (u : 𝟙_ D ⟶ G.obj (𝟙_ C)) : u = (ρ_ (𝟙_ D)).inv ≫ 𝟙_ D ◁ ε G ≫
      u ▷ G.obj (𝟙_ C) ≫ G.obj (𝟙_ C) ◁ η G ≫ (ρ_ (G.obj (𝟙_ C))).hom := by
    rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Functor.Monoidal.ε_η,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, ← rightUnitor_inv_naturality_assoc,
      Iso.inv_hom_id, Category.comp_id]
  refine ⟨?_, hμ⟩
  rw [e (ε F ≫ τ.app (𝟙_ C)), key, ← e]

/-- A natural transformation `τ` between lax monoidal functors is monoidal as soon as its
whiskering `τ ◫ H` with a faithful strong monoidal functor `H` is. -/
lemma IsMonoidal.of_whiskerRight {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (τ : F ⟶ G)
    (H : D ⥤ E) [H.Monoidal] [H.Faithful] [IsMonoidal (Functor.whiskerRight τ H)] :
    IsMonoidal τ where
  unit := by
    have h := IsMonoidal.unit (τ := Functor.whiskerRight τ H)
    simp only [Functor.LaxMonoidal.comp_ε, Functor.whiskerRight_app, Category.assoc] at h
    apply H.map_injective
    rw [← cancel_epi (ε H), H.map_comp, h]
  tensor X Y := by
    have h := IsMonoidal.tensor (τ := Functor.whiskerRight τ H) X Y
    simp only [Functor.LaxMonoidal.comp_μ, Functor.whiskerRight_app, Category.assoc,
      Functor.comp_obj] at h
    apply H.map_injective
    rw [← cancel_epi (μ H (F.obj X) (F.obj Y)), H.map_comp, h, H.map_comp,
      Functor.LaxMonoidal.μ_natural_assoc]

end NatTrans

namespace Adjunction

/-- Replacing the right adjoint of a monoidal adjunction by an isomorphic lax monoidal functor,
through a monoidal natural isomorphism, gives a monoidal adjunction. -/
lemma isMonoidal_ofNatIsoRight {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H)
    [F.OplaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] [adj.IsMonoidal]
    [NatTrans.IsMonoidal e.hom] : (adj.ofNatIsoRight e).IsMonoidal where
  leftAdjoint_ε := by
    rw [← NatTrans.IsMonoidal.unit (τ := e.hom), ← unit_app_unit_comp_map_η adj]
    simp
  leftAdjoint_μ X Y := by
    have h := NatTrans.IsMonoidal.tensor (τ := e.hom) X Y
    have h' := IsMonoidal.leftAdjoint_μ (adj := adj) X Y
    simp only [ofNatIsoRight_unit, ofNatIsoRight_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    rw [← e.hom.naturality, ← tensorHom_comp_tensorHom, δ_natural_assoc, G.map_comp,
      Category.assoc]
    erw [adj.unit_naturality_assoc]
    rw [← Category.assoc (adj.unit.app _), ← h']
    simp only [Functor.id_obj]
    rw [h]
    rw [tensorHom_comp_tensorHom_assoc]
    simp

variable {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R)
  [R.LaxMonoidal]

section Oplax

variable [L₁.OplaxMonoidal] [L₂.OplaxMonoidal] [adj₁.IsMonoidal] [adj₂.IsMonoidal]

/-- The comparison `leftAdjointUniq adj₁ adj₂ : L₁ ≅ L₂` of two left adjoints of a lax monoidal
functor, through monoidal adjunctions, is compatible with the unit comparisons. -/
@[reassoc]
lemma leftAdjointUniq_hom_app_unit_comp_η :
    (leftAdjointUniq adj₁ adj₂).hom.app (𝟙_ C) ≫ η L₂ = η L₁ :=
  conjugateEquiv_symm_app_unit_comp_η adj₂ adj₁ (𝟙 R)

/-- The comparison `leftAdjointUniq adj₁ adj₂ : L₁ ≅ L₂` of two left adjoints of a lax monoidal
functor, through monoidal adjunctions, is compatible with the tensor comparisons. -/
@[reassoc]
lemma leftAdjointUniq_hom_app_tensor_comp_δ (X Y : C) :
    (leftAdjointUniq adj₁ adj₂).hom.app (X ⊗ Y) ≫ δ L₂ X Y =
      δ L₁ X Y ≫ ((leftAdjointUniq adj₁ adj₂).hom.app X ⊗ₘ
        (leftAdjointUniq adj₁ adj₂).hom.app Y) :=
  conjugateEquiv_symm_app_tensor_comp_δ adj₂ adj₁ (𝟙 R) X Y

end Oplax

/-- The comparison `leftAdjointUniq adj₁ adj₂ : L₁ ≅ L₂` of two strong monoidal left adjoints of
a lax monoidal functor, through monoidal adjunctions, is a monoidal natural isomorphism. -/
lemma isMonoidal_leftAdjointUniq_hom [L₁.Monoidal] [L₂.Monoidal] [adj₁.IsMonoidal]
    [adj₂.IsMonoidal] : NatTrans.IsMonoidal (leftAdjointUniq adj₁ adj₂).hom :=
  .of_η_δ _ (leftAdjointUniq_hom_app_unit_comp_η adj₁ adj₂)
    (leftAdjointUniq_hom_app_tensor_comp_δ adj₁ adj₂)

end Adjunction

end CategoryTheory
