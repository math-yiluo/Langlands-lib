/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Complements on the pushforward of sheaves along a continuous functor

If the unit of a site-level adjunction `F ⊣ G` between continuous functors is an
isomorphism, then the counit of the induced adjunction
`CategoryTheory.Adjunction.sheafPushforwardContinuous` between the pushforward functors
on sheaves is an isomorphism
(`CategoryTheory.Adjunction.isIso_sheafPushforwardContinuous_counit`).

`CategoryTheory.Functor.sheafPushforwardContinuous` preserves all limits that exist in the
coefficient category
(`CategoryTheory.Functor.preservesLimitsOfShape_sheafPushforwardContinuous`): it is
precomposition with `F.op`, corestricted to the sheaf subcategories, and limits of sheaves
are created by `sheafToPresheaf` while limits of presheaves are computed pointwise. Note
that this does not go through the adjunction `F^* ⊣ F_*`, which needs extra hypotheses
(existence of the left Kan extensions and of sheafification).

A natural isomorphism of continuous functors induces an isomorphism of the pushforward
functors (`CategoryTheory.Functor.isIso_sheafPushforwardContinuousNatTrans`).

Finally, the pushforward turns a triangle identity between continuous functors `P` and `Q`
(built from composition and identity isomorphisms) into the corresponding triangle identity
for the pushforwards (`CategoryTheory.Functor.sheafPushforwardContinuous_triangle`).
-/

@[expose] public section

universe w v' u' u

open CategoryTheory Category Opposite

namespace CategoryTheory

variable {C D : Type u} [Category.{w} C] [Category.{w} D]
  (E : Type u') [Category.{v'} E]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [G.IsContinuous K J]

/-- If the unit of a site-level adjunction `F ⊣ G` is an isomorphism, then the counit of
the induced sheaf-level adjunction between the pushforward functors is an isomorphism:
its components are given by applying the sheaves to the components of the unit. -/
lemma Adjunction.isIso_sheafPushforwardContinuous_counit [IsIso adj.unit] :
    IsIso (adj.sheafPushforwardContinuous (E := E) J K).counit := by
  suffices h : ∀ P, IsIso ((adj.sheafPushforwardContinuous (E := E) J K).counit.app P) from
    NatIso.isIso_of_isIso_app _
  intro P
  have : IsIso (((adj.sheafPushforwardContinuous (E := E) J K).counit.app P).hom) := by
    suffices h : ∀ c, IsIso
        ((((adj.sheafPushforwardContinuous (E := E) J K).counit.app P).hom).app c) from
      NatIso.isIso_of_isIso_app _
    intro c
    exact inferInstanceAs (IsIso (𝟙 _ ≫ P.obj.map ((adj.unit.app c.unop).op) ≫ 𝟙 _))
  have : IsIso ((sheafToPresheaf J E).map
      ((adj.sheafPushforwardContinuous (E := E) J K).counit.app P)) := this
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

end CategoryTheory

namespace CategoryTheory.Functor

open Limits

universe w₁ w₂ vC uC vD uD vA uA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (F : C ⥤ D)
  (A : Type uA) [Category.{vA} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]

/-- The pushforward of sheaves along a continuous functor preserves limits of any shape
that exists in the coefficient category. -/
instance preservesLimitsOfShape_sheafPushforwardContinuous (E : Type w₁) [Category.{w₂} E]
    [HasLimitsOfShape E A] :
    PreservesLimitsOfShape E (F.sheafPushforwardContinuous A J K) := by
  have : PreservesLimitsOfShape E
      (F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A) :=
    preservesLimitsOfShape_of_natIso
      (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J A)

/-- The pushforward of sheaves along a continuous functor is left exact. -/
instance preservesFiniteLimits_sheafPushforwardContinuous [HasFiniteLimits A] :
    PreservesFiniteLimits (F.sheafPushforwardContinuous A J K) where
  preservesFiniteLimits _ := inferInstance

/-- A natural isomorphism of continuous functors induces an isomorphism of the pushforward
functors on sheaves. -/
instance isIso_sheafPushforwardContinuousNatTrans {F' : C ⥤ D} [F'.IsContinuous J K]
    (τ : F ⟶ F') [IsIso τ] :
    IsIso (Functor.sheafPushforwardContinuousNatTrans τ A J K) :=
  inferInstanceAs (IsIso (Functor.sheafPushforwardContinuousIso (asIso τ) A J K).inv)

section Triangle

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {A : Type*} [Category* A]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {P : D ⥤ C} {Q : C ⥤ D} {RX R'X : C ⥤ C} {RY R'Y : D ⥤ D}
  [hP : P.IsContinuous K J] [hQ : Q.IsContinuous J K] [hRX : RX.IsContinuous J J]
  [hR'X : R'X.IsContinuous J J] [hRY : RY.IsContinuous K K] [hR'Y : R'Y.IsContinuous K K]

/-- **Triangle identity for pushforwards.** Let `P : D ⥤ C` and `Q : C ⥤ D` be continuous
functors, with isomorphisms `Q ⋙ P ≅ RX ≅ R'X ≅ 𝟭` and `P ⋙ Q ≅ RY ≅ R'Y ≅ 𝟭` through
auxiliary continuous functors. If these satisfy the triangle identity
`P (𝟭 ⟶ P ⋙ Q) ≫ (Q ⋙ P ⟶ 𝟭) P = 𝟙` at the level of sites, then the induced unit
`𝟭 ≅ P_* ⋙ Q_*` and counit `Q_* ⋙ P_* ≅ 𝟭` of the pushforwards satisfy the triangle identity
`P_* η ≫ ε P_* = 𝟙`. -/
lemma sheafPushforwardContinuous_triangle (cX : Q ⋙ P ≅ RX) (cY : P ⋙ Q ≅ RY)
    (kX : R'X ≅ RX) (kY : RY ≅ R'Y) (iX : R'X ≅ 𝟭 C) (iY : R'Y ≅ 𝟭 D)
    (h : ∀ V, P.map (iY.inv.app V) ≫ P.map (kY.inv.app V) ≫ P.map (cY.inv.app V) ≫
      cX.hom.app (P.obj V) ≫ kX.inv.app (P.obj V) ≫ iX.hom.app (P.obj V) = 𝟙 _)
    (S : Sheaf J A) :
    (P.sheafPushforwardContinuous A K J).map
        (((sheafPushforwardContinuousId' iX A J).symm ≪≫ sheafPushforwardContinuousIso kX A J J ≪≫
          (sheafPushforwardContinuousComp' cX A J K J).symm).hom.app S) ≫
      (sheafPushforwardContinuousComp' cY A K J K ≪≫ sheafPushforwardContinuousIso kY A K K ≪≫
          sheafPushforwardContinuousId' iY A K).hom.app
        ((P.sheafPushforwardContinuous A K J).obj S) = 𝟙 _ := by
  ext V
  have := congrArg (fun f ↦ S.obj.map f.op) (h V.unop)
  simp only [op_comp, Functor.map_comp, op_id, Category.assoc] at this
  simp only [id_obj, comp_obj, Iso.trans_hom, Iso.symm_hom, sheafPushforwardContinuousIso_hom,
    NatTrans.comp_app, map_comp, assoc, ObjectProperty.FullSubcategory.comp_hom,
    sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
    sheafPushforwardContinuous_map_hom_app, sheafPushforwardContinuousId'_inv_app_hom_app,
    whiskerRight_app, op_obj, NatTrans.op_app, sheafPushforwardContinuousComp'_inv_app_hom_app,
    sheafPushforwardContinuousComp'_hom_app_hom_app, sheafPushforwardContinuous_obj_obj_map,
    Quiver.Hom.unop_op, sheafPushforwardContinuousId'_hom_app_hom_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  exact this.trans (S.obj.map_id _)

end Triangle

end CategoryTheory.Functor
