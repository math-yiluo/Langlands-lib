import Langlands.Sheaf.SliceExact

/-! # Exact restriction between slice sites and its global comparison -/

noncomputable section

universe uC vC uA vA uK vK

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Sheaf

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
variable (J : GrothendieckTopology C) (A : Type uA) [Category.{vA} A]

/-- Restriction between slice sites preserves coefficient-present limits. -/
instance overMapPullback_preservesLimitsOfShape {X Y : C} (f : X ⟶ Y)
    {K : Type uK} [Category.{vK} K] [HasLimitsOfShape K A] :
    PreservesLimitsOfShape K (J.overMapPullback A f) := by
  have : PreservesLimitsOfShape K
      (J.overMapPullback A f ⋙ sheafToPresheaf (J.over X) A) := by
    change PreservesLimitsOfShape K (sheafToPresheaf (J.over Y) A ⋙
      (Functor.whiskeringLeft _ _ _).obj (Over.map f).op)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (J.over X) A)

/-- The adjunction induced by slice composition and categorical pullback
makes restriction between slice sites preserve colimits of every size. -/
instance overMapPullback_preservesColimitsOfSize [HasPullbacks C]
    {X Y : C} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{vK,uK} (J.overMapPullback A f) :=
  ((Over.mapPullbackAdj f).sheafPushforwardContinuous
    (J.over X) (J.over Y)).leftAdjoint_preservesColimits

instance overMapPullback_preservesFiniteLimits [HasFiniteLimits A]
    {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteLimits (J.overMapPullback A f) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Global restriction to the target slice, followed by restriction along a
slice map, is canonically restriction to the source slice. -/
def overPullbackMapIso {X Y : C} (f : X ⟶ Y) :
    J.overPullback A Y ⋙ J.overMapPullback A f ≅ J.overPullback A X :=
  NatIso.ofComponents (fun F => F.pushforwardOverMapIso f)
    (fun c => by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext U
      simp)

/-- The comparison retains the same section module and uses its identity map. -/
@[simp] theorem overPullbackMapIso_hom_app_hom_app {X Y : C} (f : X ⟶ Y)
    (F : Sheaf J A) (U : (Over X)ᵒᵖ) :
    ((overPullbackMapIso J A f).hom.app F).hom.app U = 𝟙 _ := rfl

@[simp] theorem overPullbackMapIso_inv_app_hom_app {X Y : C} (f : X ⟶ Y)
    (F : Sheaf J A) (U : (Over X)ᵒᵖ) :
    ((overPullbackMapIso J A f).inv.app F).hom.app U = 𝟙 _ := rfl

/-- The global comparison agrees with Mathlib's slice-map identity comparison. -/
theorem overPullbackMapIso_id (X : C) :
    Functor.whiskerLeft (J.overPullback A X) (J.overMapPullbackId A X).hom ≫
        (Functor.rightUnitor (J.overPullback A X)).hom =
      (overPullbackMapIso J A (𝟙 X)).hom := by
  ext F U
  simp

/-- The global comparison agrees with Mathlib's slice-map composition
comparison, so successive source changes give the direct comparison. -/
theorem overPullbackMapIso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Functor.associator (J.overPullback A Z) (J.overMapPullback A g)
        (J.overMapPullback A f)).hom ≫
      Functor.whiskerLeft (J.overPullback A Z) (J.overMapPullbackComp A f g).hom ≫
        (overPullbackMapIso J A (f ≫ g)).hom =
      Functor.whiskerRight (overPullbackMapIso J A g).hom (J.overMapPullback A f) ≫
        (overPullbackMapIso J A f).hom := by
  ext F U
  simp

end Langlands.Sheaf
