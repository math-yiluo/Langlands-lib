/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Tensor comparison squares with explicitly supplied Hom adjunctions -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory Opposite
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : Type u₄} [Category.{v₄} J]
  {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D}
  {TE : E ⥤ E ⥤ E} {TJ : J ⥤ J ⥤ J}
  {HC : Cᵒᵖ ⥤ C ⥤ C} {HD : Dᵒᵖ ⥤ D ⥤ D}
  {HE : Eᵒᵖ ⥤ E ⥤ E} {HJ : Jᵒᵖ ⥤ J ⥤ J}

/-- Evaluation comparison using the supplied, rather than inferred, Hom adjunction.
Source: tensor--Hom adjunction, Stacks 07A4.
(blueprint: lem-sf-parametrized-tensor-hom-square). -/
def paramTensorComparisonHom (aC : TC ⊣₂ HC)
    (aD : TD ⊣₂ HD) (F : C ⥤ D)
    (t : Functor.uncurry.obj TC ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj TD) (K M : C) :
    F.obj ((HC.obj (op K)).obj M) ⟶ (HD.obj (op (F.obj K))).obj (F.obj M) :=
  (aD.adj (F.obj K)).homEquiv _ _
    (t.inv.app (K, (HC.obj (op K)).obj M) ≫ F.map ((aC.adj K).counit.app M))

private theorem comparison_comp
    (aC : TC ⊣₂ HC) (aD : TD ⊣₂ HD)
    (aE : TE ⊣₂ HE) (F : C ⥤ D) (G : D ⥤ E)
    (t : Functor.uncurry.obj TC ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj TD)
    (s : Functor.uncurry.obj TD ⋙ G ≅
      G.prod G ⋙ Functor.uncurry.obj TE) (K M : C) :
    (aE.homEquiv (X₁ := G.obj (F.obj K))).symm
      (G.map (paramTensorComparisonHom aC aD F t K M) ≫
        paramTensorComparisonHom aD aE G s (F.obj K) (F.obj M)) =
      s.inv.app (F.obj K, F.obj ((HC.obj (op K)).obj M)) ≫
        G.map (t.inv.app (K, (HC.obj (op K)).obj M)) ≫
        G.map (F.map ((aC.adj K).counit.app M)) := by
  rw [aE.homEquiv_symm_naturality_two]
  simp only [paramTensorComparisonHom, ← ParametrizedAdjunction.homEquiv_eq,
    Equiv.symm_apply_apply]
  have hn := s.inv.naturality
    (Prod.mkHom (𝟙 (F.obj K)) (paramTensorComparisonHom aC aD F t K M))
  simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp] at hn
  change (TE.obj (G.obj (F.obj K))).map
      (G.map (paramTensorComparisonHom aC aD F t K M)) ≫
      s.inv.app (F.obj K, (HD.obj (op (F.obj K))).obj (F.obj M)) ≫
      G.map ((aD.adj (F.obj K)).counit.app (F.obj M)) = _
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
  have hev : (TD.obj (F.obj K)).map (paramTensorComparisonHom aC aD F t K M) ≫
      (aD.adj (F.obj K)).counit.app (F.obj M) =
      t.inv.app (K, (HC.obj (op K)).obj M) ≫
        F.map ((aC.adj K).counit.app M) := by
    exact ((aD.adj (F.obj K)).homEquiv _ _).symm_apply_apply _
  rw [hev, G.map_comp]

end CategoryTheory
