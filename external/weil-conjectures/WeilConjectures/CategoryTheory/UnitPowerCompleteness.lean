/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
import WeilConjectures.AlgebraicGeometry.RingedLocalizationRestriction

set_option linter.privateModule false

/-!
# Derived completeness under a unit times a positive power

Source: Stacks Project, algebraization.tex, Tags 099B, 099E and 099F
(auxiliary; not a blueprint node).

The principal ideal sheaf is the categorical image of multiplication by its generator.
Thus its sections include locally divisible sections, without requiring a global coefficient.
The comparison uses the actual two-term complexes and their augmentation-induced units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory

-- Cache this site-independent proof instead of repeating the general limit-preservation
-- instance search at every occurrence of the underlying ring sheaf.
private theorem unitPower_hasSheafCompose
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

-- Cache this site-independent proof instead of repeating the general limit-preservation
-- instance search at every occurrence of the underlying ring sheaf.
attribute [local instance] unitPower_hasSheafCompose

private abbrev sectionValue
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) : O.obj.obj X := s.val X

private def unitGenerators
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (R : Sheaf K RingCat.{u}) : (SheafOfModules.unit R).GeneratingSections where
  I := ULift.{u} (Fin 1)
  s _ := (SheafOfModules.unit R).unitHomEquiv (𝟙 _)
  epi := by
    have h : SheafOfModules.ιFree (R := R) (⟨0⟩ : ULift.{u} (Fin 1)) ≫
        (SheafOfModules.unit R).freeHomEquiv.symm
          (fun _ : ULift.{u} (Fin 1) ↦ (SheafOfModules.unit R).unitHomEquiv (𝟙 _)) = 𝟙 _ := by
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    exact epi_of_epi_fac h

private theorem principal_generators
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (c : (O.obj ⋙ forget CommRingCat).sections) (U : C) :
    IsRingedIdealGeneratingList O (image (ringedKoszulScalar O c).asHom)
      (image.ι (ringedKoszulScalar O c).asHom) U 1 (fun _ ↦ c.val (op U)) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let p := factorThruImage (ringedKoszulScalar O c).asHom
  let σ := (unitGenerators (R.over U)).ofEpi (p.over U)
  refine ⟨σ, Equiv.ulift, ?_⟩
  intro i
  have h := congrArg (fun f ↦ f.val.app (op U)) (image.fac (ringedKoszulScalar O c).asHom)
  have h' := DFunLike.congr_fun (congrArg (fun f ↦ f.hom) h) (1 : O.obj.obj (op U))
  change (image.ι (ringedKoszulScalar O c).asHom).val.app (op U)
    (p.val.app (op U) (show R.obj.obj (op U) from 1)) = c.val (op U)
  refine h'.trans ?_
  change (1 : O.obj.obj (op U)) * sectionValue O c (op U) = sectionValue O c (op U)
  exact one_mul _

namespace UnitPowerRestriction

section ModuleRestriction
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F J K] [F.IsCocontinuous J K]
  (O : Sheaf K CommRingCat.{u})
end ModuleRestriction

section ComplexRestriction
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (O : Sheaf K CommRingCat.{u}) (P : Sheaf J CommRingCat.{u})
  (V : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj O) ⥤
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj P)) [V.Additive]
  (s : (O.obj ⋙ forget CommRingCat).sections)
  (t : (P.obj ⋙ forget CommRingCat).sections)
  (h : Arrow.mk (V.map (ringedSectionLocalizationUnit O s)) ≅
    Arrow.mk (ringedSectionLocalizationUnit P t))

end ComplexRestriction

end UnitPowerRestriction

end CategoryTheory
