/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

set_option linter.privateModule false

/-!
# Localization complexes and derived internal Hom on a ringed site

Source: Stacks Project, Cohomology on Sites, Tags 08J9 and 08JB;
Algebraization of Formal Spaces, Tag 0996
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

private theorem localization_isFlat (R : Sheaf J CommRingCat.{u})
    (g : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    SheafOfModules.IsFlat (ringedSectionLocalization R g) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let F := ringedSectionLocalizationPresheaf R g
  have hflat (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := by
    dsimp [F, ringedSectionLocalizationPresheaf, ringedSectionLocalizationCarrier]
    infer_instance
  have hF : PreservesFiniteLimits (tensorRight F) := by
    constructor
    intro K _ _
    have (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := hflat V
    exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V ↦ isLimitOfPreserves
        (tensorRight (show ModuleCat (R.obj.obj V) from F.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective J (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective J (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ ↦ Function.surjective_id)
  exact (PresheafOfModules.isFlat_sheafification_obj (R := R) (𝟙 O.obj) F hF).2

end CategoryTheory
