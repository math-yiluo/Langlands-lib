/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ModuleCupNaiveMap
/-! # Tensor-counit normalization of the global pullback

Source: Stacks Tags 008A, 008Y, 0B6A and 0FKU. -/

@[expose] public section
universe u
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable (X : Scheme.{u})
local instance globalSectionsLaxDataCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalSectionsLaxDataMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalSectionsLaxDataSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
attribute [local instance]
  instHasColimitsOfSizeSheafOfModulesOpensCarrierCarrierCommRingCatToRingedSpaceModuleRings
local instance globalSectionsLaxDataPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalSectionsLaxDataClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
private theorem globalSectionsTensor_natural_left
    {M N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (f : M ⟶ N)
    (P : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f ▷
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj P ≫
      moduleCup_sectionTensorMap X N P = moduleCup_sectionTensorMap X M P ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (f ▷ P) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    moduleCup_sectionTensorMap, ModuleCat.hom_ofHom]
  exact (whiskerRight_app_tmulSection (X := X) (N := P) (U := ⊤) f x y).symm

private theorem globalSectionsTensor_natural_right
    {M N : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (P : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (f : M ⟶ N) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj P ◁
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f ≫
      moduleCup_sectionTensorMap X P N = moduleCup_sectionTensorMap X P M ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (P ◁ f) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    moduleCup_sectionTensorMap, ModuleCat.hom_ofHom]
  exact (whiskerLeft_app_tmulSection (X := X) (M := P) (U := ⊤) f x y).symm

private theorem globalSectionsTensor_associativity
    (M N P : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    moduleCup_sectionTensorMap X M N ▷
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj P ≫
      moduleCup_sectionTensorMap X (M ⊗ N) P ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (α_ M N P).hom =
      (α_ ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N)
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj P)).hom ≫
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M ◁
        moduleCup_sectionTensorMap X N P ≫ moduleCup_sectionTensorMap X M (N ⊗ P) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    moduleCup_sectionTensorMap, ModuleCat.hom_ofHom]
  exact associator_hom_app_tmulSection (X := X) (M := M) (N := N) (P := P)
    (U := ⊤) x y z

private theorem globalSectionsTensor_left_unitality
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (λ_ ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)).hom =
      ModuleCat.ofHom (R := Γ(X, ⊤)) (unitSectionsEquiv (X := X) ⊤).toLinearMap ▷
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M ≫
      moduleCup_sectionTensorMap X (𝟙_ _) M ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (λ_ M).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro r s
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    moduleCup_sectionTensorMap, ModuleCat.hom_ofHom]
  exact (leftUnitor_hom_app_tmulSection (X := X) (M := M) (U := ⊤) r s).symm

private theorem globalSectionsTensor_right_unitality
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (ρ_ ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)).hom =
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M ◁
        ModuleCat.ofHom (R := Γ(X, ⊤)) (unitSectionsEquiv (X := X) ⊤).toLinearMap ≫
      moduleCup_sectionTensorMap X M (𝟙_ _) ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (ρ_ M).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s r
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    moduleCup_sectionTensorMap, ModuleCat.hom_ofHom]
  exact (rightUnitor_hom_app_tmulSection (X := X) (M := M) (U := ⊤) r s).symm

set_option backward.isDefEq.respectTransparency true in
/-- The canonical lax structure has the concrete unit and tensor maps.
Source: Stacks, Section 17.16 (Tag 01CA), the sheaf tensor construction;
WeilConjectures.AlgebraicGeometry.Modules.TensorSection, the section tensor identities.
(blueprint: lem-sc-global-sections-lax-monoidal-data)
Proof: choose the unit map induced by unitSectionsEquiv and the tensorator induced
by the bilinear pairing tmulSection. Naturality in either argument follows by applying
whiskerRight_app_tmulSection and whiskerLeft_app_tmulSection to pure tensors.
The associativity diagram agrees on every triple of pure tensors by
associator_hom_app_tmulSection: both sides give the nested tensor section with
parentheses changed by the sheaf associator. The left and right unit diagrams agree
on pure tensors by leftUnitor_hom_app_tmulSection and rightUnitor_hom_app_tmulSection:
both sides send r tensor s (respectively s tensor r) to r times s.
TensorProduct.ext' and ModuleCat.hom_ext extend these identities to all morphisms,
so the prescribed maps define a lax monoidal structure. Its unit and tensorator
are the required maps by construction. The same equations hold for zero modules
and the empty scheme; no injectivity or surjectivity of the tensorator is asserted. -/
theorem globalSectionsFunctor_laxMonoidal_data
    :
    ∃ lax : (RingedSpace.globalSectionsFunctor X.toRingedSpace).LaxMonoidal,
      letI := lax
      Functor.LaxMonoidal.ε (RingedSpace.globalSectionsFunctor X.toRingedSpace) =
          ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap ∧
      ∀ M N, Functor.LaxMonoidal.μ (RingedSpace.globalSectionsFunctor X.toRingedSpace) M N =
          moduleCup_sectionTensorMap X M N := by
  exact ⟨{
    ε := ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap
    μ := moduleCup_sectionTensorMap X
    μ_natural_left := globalSectionsTensor_natural_left X
    μ_natural_right := globalSectionsTensor_natural_right X
    associativity := globalSectionsTensor_associativity X
    left_unitality := globalSectionsTensor_left_unitality X
    right_unitality := globalSectionsTensor_right_unitality X }, rfl, fun _ _ ↦ rfl⟩

end
end AlgebraicGeometry.Scheme.Modules
