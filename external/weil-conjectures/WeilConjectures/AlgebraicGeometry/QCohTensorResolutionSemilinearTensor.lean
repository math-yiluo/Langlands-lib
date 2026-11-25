/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSemilinear
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
open Scheme.Modules
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance semilinearTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The restriction tensor comparison carries the restricted pure section to the
pure section of the restrictions. -/
theorem tensorResolutionRestrictionTensor_unit {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (F G : Y.Modules) (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    (tensorResolutionRestrictionTensor j F G).hom.app ⊤
      (((restrictAdjunction j).unit.app (F ⊗ G)).app ⊤ (tmulSection s t)) =
    tmulSection (M := F.restrict j) (N := G.restrict j) (U := ⊤)
      (((restrictAdjunction j).unit.app F).app ⊤ s)
      (((restrictAdjunction j).unit.app G).app ⊤ t) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((tensorResolutionRestrictionTensor j F G).inv.app ⊤)).injective
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id]
  change ((restrictAdjunction j).unit.app (F ⊗ G)).app ⊤ (tmulSection s t) = _
  rw [tensorResolutionRestrictionTensor_inv_tmul]
  exact tmulSection_map (M := F) (N := G) (j.image_preimage_le ⊤) s t

/-- The equation on pure tensors determines the sheafified tensor chain map. -/
theorem tensorResolutionSemilinearMap_tensor {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    (M N : ModuleCat.{u} A) (M' N' : ModuleCat.{u} B)
    (a : M ⟶ (ModuleCat.restrictScalars φ.hom).obj M')
    (b : N ⟶ (ModuleCat.restrictScalars φ.hom).obj N')
    (k : M ⊗ N ⟶ (ModuleCat.restrictScalars φ.hom).obj (M' ⊗ N'))
    (hk : ∀ (x : M) (y : N), k (x ⊗ₜ[A] y) =
      (show M' from a x) ⊗ₜ[B] (show N' from b y)) :
    (restrictFunctor (Spec.map φ)).map (tensorResolutionTildeTensorHom A M N) ≫
        (tensorResolutionRestrictionTensor (Spec.map φ) (tilde M) (tilde N)).hom ≫
        (tensorResolutionSemilinearMap φ a ⊗ₘ tensorResolutionSemilinearMap φ b) =
      tensorResolutionSemilinearMap φ k ≫ tensorResolutionTildeTensorHom B M' N' := by
  apply ((tensorResolutionSemilinearAdjunction φ).homEquiv (M ⊗ N)
    (tilde M' ⊗ tilde N')).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (tensorResolutionSemilinearMap φ a ⊗ₘ tensorResolutionSemilinearMap φ b).app ⊤
      ((tensorResolutionRestrictionTensor (Spec.map φ) (tilde M) (tilde N)).hom.app ⊤
        (((restrictFunctor (Spec.map φ)).map (tensorResolutionTildeTensorHom A M N)).app ⊤
          (((restrictAdjunction (Spec.map φ)).unit.app (tilde (M ⊗ N))).app ⊤
            (tilde.toOpen (M ⊗ N) ⊤ (x ⊗ₜ[A] y))))) =
    (tensorResolutionTildeTensorHom B M' N').app ⊤
      ((tensorResolutionSemilinearMap φ k).app ⊤
        (((restrictAdjunction (Spec.map φ)).unit.app (tilde (M ⊗ N))).app ⊤
          (tilde.toOpen (M ⊗ N) ⊤ (x ⊗ₜ[A] y))))
  have hu := congrArg (fun f ↦ f.app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (x ⊗ₜ[A] y)))
    ((restrictAdjunction (Spec.map φ)).unit.naturality (tensorResolutionTildeTensorHom A M N))
  change ((restrictAdjunction (Spec.map φ)).unit.app (tilde M ⊗ tilde N)).app ⊤
      ((tensorResolutionTildeTensorHom A M N).app ⊤
        (tilde.toOpen (M ⊗ N) ⊤ (x ⊗ₜ[A] y))) =
    (((restrictFunctor (Spec.map φ)).map (tensorResolutionTildeTensorHom A M N)).app ⊤
      (((restrictAdjunction (Spec.map φ)).unit.app (tilde (M ⊗ N))).app ⊤
        (tilde.toOpen (M ⊗ N) ⊤ (x ⊗ₜ[A] y)))) at hu
  rw [← hu, tensorResolutionTildeTensorHom_tmul, tensorResolutionRestrictionTensor_unit,
    tensorHom_app_tmulSection, tensorResolutionSemilinearMap_unit,
    tensorResolutionSemilinearMap_unit, tensorResolutionSemilinearMap_unit, hk,
    tensorResolutionTildeTensorHom_tmul]

end AlgebraicGeometry
