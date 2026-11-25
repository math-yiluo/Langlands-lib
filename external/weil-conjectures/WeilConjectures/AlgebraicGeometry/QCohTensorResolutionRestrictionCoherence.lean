/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartRestriction
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTensorNaturality
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionHomologyComposition

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
open Scheme.Modules
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionRestrictionCoherence_localInst1 (X :
  Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionRestrictionCoherence_localInst2 (X :
  Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionRestrictionCoherence_localInst3 (X : Scheme.{u}) :
  (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionRestrictionCoherence_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Restricting a module morphism uses its section map on the image open. -/
theorem tensorResolution_restrict_map_apply {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {F G : Y.Modules} (f : F ⟶ G)
    (W : X.Opens) (s : Γ(F.restrict j, W)) :
    ((restrictFunctor j).map f).app W s = f.app (j ''ᵁ W) s := rfl

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Pure tensor sections commute with any presheaf restriction map. -/
theorem tensorResolution_presheaf_map_tmul {X : Scheme.{u}} (F G : X.Modules)
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (s : Γ(F, U.unop)) (t : Γ(G, U.unop)) :
    (F ⊗ G).presheaf.map i (tmulSection s t) =
      tmulSection (F.presheaf.map i s) (G.presheaf.map i t) := by
  have ht := tmulSection_map (M := F) (N := G) (leOfHom i.unop) s t
  change (F ⊗ G).presheaf.map i (tmulSection s t) =
    tmulSection (F.presheaf.map i s) (G.presheaf.map i t) at ht
  exact ht

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The normalized tensor restriction comparisons respect successive affine restrictions. -/
theorem tensorResolutionChartRestriction_tensor_inv (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) (F G : Y.Modules) :
    (((tensorResolutionChartRestrictionIso Y V U h).hom.app F) ⊗ₘ
        ((tensorResolutionChartRestrictionIso Y V U h).hom.app G)) ≫
        (tensorResolutionRestrictionTensor V.2.fromSpec F G).inv =
      (tensorResolutionRestrictionTensor (Spec.map (Y.presheaf.map (homOfLE h).op))
        (F.restrict U.2.fromSpec) (G.restrict U.2.fromSpec)).inv ≫
        (restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
          (tensorResolutionRestrictionTensor U.2.fromSpec F G).inv ≫
        (tensorResolutionChartRestrictionIso Y V U h).hom.app (F ⊗ G) := by
  apply tensorResolution_tensor_hom_ext
  intro W s t
  simp only [Hom.comp_app, ConcreteCategory.comp_apply,
    tensorHom_app_tmulSection, tensorResolutionRestrictionTensor_inv_tmul]
  simp only [tensorResolutionChartRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app]
  simp only [tensorResolution_restrict_map_apply]
  erw [tensorResolutionRestrictionTensor_inv_tmul
    (Spec.map (Y.presheaf.map (homOfLE h).op))
    (F.restrict U.2.fromSpec) (G.restrict U.2.fromSpec) W s t]
  -- Identify sections explicitly instead of comparing the nested restriction functors.
  erw [tensorResolutionRestrictionTensor_inv_tmul U.2.fromSpec F G
    ((Spec.map (Y.presheaf.map (homOfLE h).op)) ''ᵁ W)
    (((F.restrict U.2.fromSpec).restrictAppIso
      (Spec.map (Y.presheaf.map (homOfLE h).op)) W).hom s)
    (((G.restrict U.2.fromSpec).restrictAppIso
      (Spec.map (Y.presheaf.map (homOfLE h).op)) W).hom t)]
  -- Only the right side contains presheaf maps applied to pure tensors.
  conv_rhs =>
    erw [tensorResolution_presheaf_map_tmul F G, tensorResolution_presheaf_map_tmul F G]
  rfl

end AlgebraicGeometry
