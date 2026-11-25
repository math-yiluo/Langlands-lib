/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.CechPullback.CechPullbackAugmentedTensorComparison

/-! # Steps of the augmented Cech pullback induction.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E; sites-modules.tex, Tag 03EL.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory
set_option maxHeartbeats 2000000 in
-- The successor clause contains several chosen total-complex instances.
/-- One successor step of the finite Cech comparison, including its augmentation.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E.
Proof: expand the successor clause of ringedExtendedCech. The adjunction makes F additive
and preserves the coproducts of totalization. Apply t in each bidegree to obtain the
comparison from F of the tensor complex to the tensor of the images. Naturality of t
makes it commute with both signed differentials. The inverse comparison on coproduct
summands gives its inverse. Compose with the tensor of the factor isomorphism and ly.
For augmentation compatibility, precompose in each degree with every image of a tensor
summand inclusion. Naturality replaces both augmentations by their images under F;
the factor equation and hy reduce the calculation to the normalized unit equation hu.
The degree-zero single-complex comparison is the unit identification and the other target
components vanish. Coproduct extensionality gives the asserted chain-map equality.
(blueprint: lem-weil-pbc-cech-pullback-augmented-tensor-step) -/
theorem cech_pullback_augmented_tensor_step
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (h : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (F : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    [F.PreservesZeroMorphisms] (hF : F ⊣ h.modules)
    (v : F.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (t : ∀ X Y, F.obj (@MonoidalCategory.tensorObj _ _
        (SheafOfModules.monoidalCategory R).toMonoidalCategoryStruct X Y) ≅
      @MonoidalCategory.tensorObj _ _
        (SheafOfModules.monoidalCategory S).toMonoidalCategoryStruct (F.obj X) (F.obj Y))
    (ht : letI := SheafOfModules.monoidalCategory R
      let := SheafOfModules.monoidalCategory S
      ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
        F.map (f ⊗ₘ g) ≫ (t X' Y').hom =
          (t X Y).hom ≫ (F.map f ⊗ₘ F.map g))
    (hu : letI := SheafOfModules.monoidalCategory R
      let := SheafOfModules.monoidalCategory S
      (t (𝟙_ _) (𝟙_ _)).hom ≫ (v.hom ⊗ₘ v.hom) ≫ (λ_ (𝟙_ _)).hom =
        F.map (λ_ (𝟙_ _)).hom ≫ v.hom)
    (r : ℕ) (b : Fin (r + 1) → (R.obj ⋙ forget CommRingCat).sections)
    (c : Fin (r + 1) → (S.obj ⋙ forget CommRingCat).sections)
    (hfactor : ∃ l : (F.mapHomologicalComplex (.up ℤ)).obj (ringedLocalizationTwoTerm R (b 0)) ≅
          ringedLocalizationTwoTerm S (c 0),
        l.hom ≫ ringedLocalizationTwoTermAugmentation S (c 0) =
          (F.mapHomologicalComplex (.up ℤ)).map
              (ringedLocalizationTwoTermAugmentation R (b 0)) ≫
            (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
              (SheafOfModules.unit
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map v.hom)
    (ly : (F.mapHomologicalComplex (.up ℤ)).obj
        (ringedExtendedCech R r (fun i ↦ b i.succ)).1 ≅
      (ringedExtendedCech S r (fun i ↦ c i.succ)).1)
    (hy : ly.hom ≫ (ringedExtendedCech S r (fun i ↦ c i.succ)).2 =
      (F.mapHomologicalComplex (.up ℤ)).map
        (ringedExtendedCech R r (fun i ↦ b i.succ)).2 ≫
          (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map v.hom) :
    ∃ l : ((F.mapHomologicalComplex (.up ℤ)).obj (ringedExtendedCech R (r + 1) b).1) ≅
        (ringedExtendedCech S (r + 1) c).1,
      l.hom ≫ (ringedExtendedCech S (r + 1) c).2 =
        (F.mapHomologicalComplex (.up ℤ)).map (ringedExtendedCech R (r + 1) b).2 ≫
          (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map v.hom := by
  have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.symmetricCategory S
  have := Classical.choice (SheafOfModules.tensorClosed R).1
  have := Classical.choice (SheafOfModules.tensorClosed S).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  let := Classical.choice (SheafOfModules.tensorClosed S).2.1
  have := hF.isLeftAdjoint
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  obtain ⟨lx, hx⟩ := hfactor
  exact CechPullback.augmented_tensor F t ht h.modules hF v hu
    (ringedLocalizationTwoTerm R (b 0))
    (ringedExtendedCech R r (fun i ↦ b i.succ)).1
    (ringedLocalizationTwoTerm S (c 0))
    (ringedExtendedCech S r (fun i ↦ c i.succ)).1
    (ringedLocalizationTwoTermAugmentation R (b 0))
    (ringedExtendedCech R r (fun i ↦ b i.succ)).2
    (ringedLocalizationTwoTermAugmentation S (c 0))
    (ringedExtendedCech S r (fun i ↦ c i.succ)).2 lx ly hx hy
end CategoryTheory
