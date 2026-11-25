/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedCoefficientProjectionData
import WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

set_option linter.privateModule false

/-! # The canonical inverse-image coefficient comparison

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

attribute [local instance] SheafOfModules.sheafHasBinaryProduct

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)

private def addMap {R : Sheaf J CommRingCat.{r}} (M : Mod J R) :
    (underlying R).obj M ⨯ (underlying R).obj M ⟶ (underlying R).obj M :=
  ⟨{ app := fun U ↦ ↾fun t ↦
        (show M.val.obj U from (prod.fst : _ ⟶ (underlying R).obj M).hom.app U t) +
        (show M.val.obj U from (prod.snd : _ ⟶ (underlying R).obj M).hom.app U t)
     naturality := by
       intro U V f
       ext t
       have h₁ := CategoryTheory.congr_fun
         ((prod.fst : (underlying R).obj M ⨯ (underlying R).obj M ⟶
           (underlying R).obj M).hom.naturality f) t
       have h₂ := CategoryTheory.congr_fun
         ((prod.snd : (underlying R).obj M ⨯ (underlying R).obj M ⟶
           (underlying R).obj M).hom.naturality f) t
       change _ = M.val.map f (_ + _)
       rw [map_add]
       exact congrArg₂ (· + ·) h₁ h₂ }⟩

private def smulMap {R : Sheaf J CommRingCat.{r}} (M : Mod J R) :
    (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
      (underlying R).obj M ⟶ (underlying R).obj M :=
  ⟨{ app := fun U ↦ ↾fun t ↦
        (show R.obj.obj U from (prod.fst : _ ⟶
          (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R).hom.app U t) •
        (show M.val.obj U from (prod.snd : _ ⟶ (underlying R).obj M).hom.app U t)
     naturality := by
       intro U V f
       ext t
       have h₁ := CategoryTheory.congr_fun
         ((prod.fst : (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
           (underlying R).obj M ⟶
           (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R).hom.naturality f) t
       have h₂ := CategoryTheory.congr_fun
         ((prod.snd : (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
           (underlying R).obj M ⟶ (underlying R).obj M).hom.naturality f) t
       change _ = M.val.map f (_ • _)
       rw [M.val.map_smul]
       exact congrArg₂ (· • ·) h₁ h₂ }⟩

private def imagePair [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.obj (A ⨯ B)).obj.obj U :=
  (inv (prodComparison uInv A B)).hom.app U
    (SheafOfModules.sectionPair (uInv.obj A) (uInv.obj B) U x y)

omit [EssentiallySmall.{r} C] in
private theorem imagePair_fst [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.map (prod.fst : A ⨯ B ⟶ A)).hom.app U (imagePair A B U x y) = x := by
  change (inv (prodComparison uInv A B) ≫ uInv.map prod.fst).hom.app U _ = x
  rw [← prodComparison_fst, IsIso.inv_hom_id_assoc]
  exact SheafOfModules.sectionPair_fst _ _ _ _ _

omit [EssentiallySmall.{r} C] in
private theorem imagePair_snd [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.map (prod.snd : A ⨯ B ⟶ B)).hom.app U (imagePair A B U x y) = y := by
  change (inv (prodComparison uInv A B) ≫ uInv.map prod.snd).hom.app U _ = y
  rw [← prodComparison_snd, IsIso.inv_hom_id_assoc]
  exact SheafOfModules.sectionPair_snd _ _ _ _ _

end SheafOfModules.RingedCoefficientProjection

end
