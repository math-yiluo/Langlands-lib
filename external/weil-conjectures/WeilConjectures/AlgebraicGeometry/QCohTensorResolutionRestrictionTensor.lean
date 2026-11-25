/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionAffineModel
public import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance restrictionTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance restrictionPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules := (SheafOfModules.tensorClosed X.sheaf).1.some
local instance restrictionZero (X : Scheme.{u}) :
    (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance restrictionObjZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false in
theorem tensorResolution_tensor_hom_ext {X : Scheme.{u}} {F G H : X.Modules}
    {a b : F ⊗ G ⟶ H}
    (h : ∀ (U : X.Opens) (s : Γ(F, U)) (t : Γ(G, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  let β := fun U : X.Opensᵒᵖ ↦
    LinearMap.mk₂ Γ(X, U.unop) (fun s t ↦ a.app U.unop (tmulSection s t))
      (by intros; rw [add_tmulSection, map_add])
      (by intros; rw [smul_tmulSection, Hom.app_smul])
      (by intros; rw [tmulSection_add, map_add])
      (by intros; rw [tmulSection_smul, Hom.app_smul])
  have hβ : ∀ {U V : X.Opensᵒᵖ} (i : U ⟶ V) (s : Γ(F, U.unop))
      (t : Γ(G, U.unop)),
      β V (F.val.map i s) (G.val.map i t) = H.val.map i (β U s t) := by
    intro U V i s t
    change a.app V.unop (tmulSection (F.presheaf.map i s) (G.presheaf.map i t)) = _
    have hi := tmulSection_map (M := F) (N := G) (leOfHom i.unop) s t
    simp only [homOfLE_leOfHom] at hi
    exact (congrArg (a.app V.unop) hi.symm).trans
      (Hom.app_presheaf_map a i.unop _)
  obtain ⟨φ, hφ, huniq⟩ := SheafOfModules.tensor_bilinear_universal
    X.sheaf F G H β hβ
  exact (huniq a (by intro U s t; rfl)).trans (huniq b (by
    intro U s t
    exact (h U.unop s t).symm)).symm


/-- Restriction tensor comparison fixed by its formula on local pure sections. -/
noncomputable def tensorResolutionRestrictionTensor {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (F G : Y.Modules) :
    (F ⊗ G).restrict j ≅ F.restrict j ⊗ G.restrict j :=
  (exists_restriction_tensor_comparison j F G).choose

@[simp] theorem tensorResolutionRestrictionTensor_inv_tmul {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (F G : Y.Modules)
    (V : X.Opens) (s : Γ(F.restrict j, V)) (t : Γ(G.restrict j, V)) :
    (tensorResolutionRestrictionTensor j F G).inv.app V (tmulSection s t) =
      tmulSection (M := F) (N := G) (U := j ''ᵁ V) s t := by
  exact (exists_restriction_tensor_comparison j F G).choose_spec V s t

/-- Naturality of the normalized restriction tensor comparison. -/
theorem tensorResolutionRestrictionTensor_natural {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {F F' G G' : Y.Modules} (f : F ⟶ F') (g : G ⟶ G') :
    (restrictFunctor j).map (f ⊗ₘ g) ≫ (tensorResolutionRestrictionTensor j F' G').hom =
      (tensorResolutionRestrictionTensor j F G).hom ≫
        ((restrictFunctor j).map f ⊗ₘ (restrictFunctor j).map g) := by
  apply (cancel_epi (tensorResolutionRestrictionTensor j F G).inv).1
  apply (cancel_mono (tensorResolutionRestrictionTensor j F' G').inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply tensorResolution_tensor_hom_ext
  intro V s t
  simp only [Hom.comp_app, ConcreteCategory.comp_apply,
    tensorResolutionRestrictionTensor_inv_tmul, tensorHom_app_tmulSection]
  change (f ⊗ₘ g).app (j ''ᵁ V) (tmulSection s t) =
    tmulSection (f.app (j ''ᵁ V) s) (g.app (j ''ᵁ V) t)
  exact tensorHom_app_tmulSection f g s t

/-- The normalized restriction comparison, as an isomorphism of bifunctors. -/
noncomputable def tensorResolutionRestrictionTensorNatIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    (Functor.postcompose₂.obj (restrictFunctor j)).obj (curriedTensor Y.Modules) ≅
      (((Functor.whiskeringLeft₂ X.Modules).obj (restrictFunctor j)).obj
        (restrictFunctor j)).obj (curriedTensor X.Modules) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun G ↦ tensorResolutionRestrictionTensor j F G) (by
      intro G G' g
      simpa using tensorResolutionRestrictionTensor_natural j (𝟙 F) g)) (by
    intro F F' f
    ext G : 2
    simpa using tensorResolutionRestrictionTensor_natural j f (𝟙 G))

/-- Restriction of a total tensor complex, with normalized component tensor maps. -/
noncomputable def tensorResolutionRestrictionTotalIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (E F : CochainComplex Y.Modules ℤ) :
    (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules))) ≅
      CochainComplex.mapBifunctor
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E)
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F)
        (curriedTensor X.Modules) :=
  asIso (HomologicalComplex.mapBifunctorComparison
    (tensorResolutionRestrictionTensorNatIso j).hom (.up ℤ) E F)

end AlgebraicGeometry
