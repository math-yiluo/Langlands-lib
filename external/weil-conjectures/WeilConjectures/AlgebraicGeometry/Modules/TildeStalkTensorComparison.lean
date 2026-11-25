/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Tensor comparison for affine tilde stalk modules

## References

* Stacks Project, Schemes, Tag 01HV, and More on Algebra, Tag 06Y1
* Stacks Project, Schemes, Tag 01HV, item (7), and More on Algebra, Tag 06Y1, as used in Perfect
  Complexes, Tag 08DV
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

private noncomputable def stalkTensorIso (A : Type u) [CommRing A]
    (x : Spec (.of A)) (M : ModuleCat.{u} A)
    (N : ModuleCat.{u} ((Spec (.of A)).presheaf.stalk x)) :
    (ModuleCat.restrictScalars (StructureSheaf.toStalk A x).hom).obj
      (N ⊗ ((RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace x).obj
        (tilde (R := .of A) M))) ≅
    (ModuleCat.restrictScalars (StructureSheaf.toStalk A x).hom).obj N ⊗ M := by
  let : Algebra A ((Spec (.of A)).presheaf.stalk x) :=
    (StructureSheaf.toStalk A x).hom.toAlgebra
  have : IsLocalization x.asIdeal.primeCompl ((Spec (.of A)).presheaf.stalk x) :=
    inferInstanceAs (IsLocalization x.asIdeal.primeCompl
      ((structurePresheafInCommRingCat A).stalk x))
  have : IsScalarTower A ((Spec (.of A)).presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := PrimeSpectrum.Top A)
        (moduleStructurePresheaf A M).presheaf x) :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  let : Module A N := Module.compHom N (StructureSheaf.toStalk A x).hom
  have : IsScalarTower A ((Spec (.of A)).presheaf.stalk x) N :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  exact ((IsLocalizedModule.isBaseChange x.asIdeal.primeCompl
    ((Spec (.of A)).presheaf.stalk x)
      (StructureSheaf.toStalkₗ A M x)).tensorEquiv N).restrictScalars A
    |>.toModuleIso

private theorem stalkTensorIso_inv_tmul (A : Type u) [CommRing A]
    (x : Spec (.of A)) (M : ModuleCat.{u} A)
    (N : ModuleCat.{u} ((Spec (.of A)).presheaf.stalk x)) (n : N) (m : M) :
    (stalkTensorIso A x M N).inv
      ((show (ModuleCat.restrictScalars (StructureSheaf.toStalk A x).hom).obj N from n)
        ⊗ₜ[A] m) =
      n ⊗ₜ[(Spec (.of A)).presheaf.stalk x] (StructureSheaf.toStalkₗ A M x m) := by
  let : Algebra A ((Spec (.of A)).presheaf.stalk x) :=
    (StructureSheaf.toStalk A x).hom.toAlgebra
  have : IsLocalization x.asIdeal.primeCompl ((Spec (.of A)).presheaf.stalk x) :=
    inferInstanceAs (IsLocalization x.asIdeal.primeCompl
      ((structurePresheafInCommRingCat A).stalk x))
  have : IsScalarTower A ((Spec (.of A)).presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := PrimeSpectrum.Top A)
        (moduleStructurePresheaf A M).presheaf x) :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  let : Module A N := Module.compHom N (StructureSheaf.toStalk A x).hom
  have : IsScalarTower A ((Spec (.of A)).presheaf.stalk x) N :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  change (LinearEquiv.lTensor N
    (IsLocalizedModule.isBaseChange x.asIdeal.primeCompl
      ((Spec (.of A)).presheaf.stalk x) (StructureSheaf.toStalkₗ A M x)).equiv)
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A _ _ N M).symm
      (n ⊗ₜ[A] m)) = _
  simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]

private theorem stalk_map_toStalk (A : Type u) [CommRing A]
    (x : Spec (.of A)) {M M' : ModuleCat.{u} A}
    (f : M ⟶ M') (m : M) :
    ((RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace x).map (tilde.map f))
      (StructureSheaf.toStalkₗ A M x m) = StructureSheaf.toStalkₗ A M' x (f m) := by
  dsimp only [StructureSheaf.toStalkₗ, RingedSpace.moduleStalkFunctor,
    RingedSpace.moduleStalkMap, RingedSpace.stalkAddMap]
  change (TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    ((PresheafOfModules.toPresheaf _).map (tilde.map f).val)
      (TopCat.Presheaf.germ (moduleStructurePresheaf A M).presheaf ⊤ x
        (by simp) (StructureSheaf.toOpenₗ A M ⊤ m)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have h := tilde.toOpen_map_app (R := .of A) f ⊤
  have h' := congr($h m)
  change TopCat.Presheaf.germ (moduleStructurePresheaf A M').presheaf ⊤ x _ _ =
    TopCat.Presheaf.germ (moduleStructurePresheaf A M').presheaf ⊤ x _ _
  congr 1

/-- The tensor comparison
for individual associated-sheaf stalks is natural in both modules. No acyclicity
or K-flatness assumption is needed. -/
theorem nonempty_restrictScalars_tensor_tildeStalkNatIso
    (A : Type u) [CommRing A] (x : Spec (.of A)) :
    let S := tilde.functor (.of A) ⋙
      RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace x
    let U := ModuleCat.restrictScalars (StructureSheaf.toStalk A x).hom
    Nonempty
      ((Functor.postcompose₂.obj U).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj S).obj (curriedTensor _)) ≅
      (((Functor.whiskeringLeft₂ _).obj U).obj (𝟭 _)).obj (curriedTensor _)) := by
  classical
  let S := tilde.functor (.of A) ⋙
    RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace x
  refine ⟨(NatIso.ofComponents (fun N ↦
    NatIso.ofComponents (fun M ↦ (stalkTensorIso A x M N).symm) ?_) ?_).symm⟩
  · intro M M' f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro n m
    change (stalkTensorIso A x M' _).inv (n ⊗ₜ[A] f m) =
      ((curriedTensor _).obj _).map (S.map f)
        ((stalkTensorIso A x M _).inv (n ⊗ₜ[A] m))
    rw [stalkTensorIso_inv_tmul, stalkTensorIso_inv_tmul]
    change _ = n ⊗ₜ[_] (S.map f) (StructureSheaf.toStalkₗ A M x m)
    congr 1
    exact (stalk_map_toStalk A x f m).symm
  · intro N N' g
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro n m
    change (stalkTensorIso A x M N').inv (g n ⊗ₜ[A] m) =
      (g ▷ S.obj M) ((stalkTensorIso A x M N).inv (n ⊗ₜ[A] m))
    rw [stalkTensorIso_inv_tmul, stalkTensorIso_inv_tmul]
    rfl


end AlgebraicGeometry
