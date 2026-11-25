/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

/--
There is an A-linear equivalence from the localization of Y to its scalar extension
that carries the localized range of f to the range of the scalar-extended map.
Use `LocalizedModule.equivTensorProduct` and
`LinearMap.localized'_range_eq_range_localizedMap`, then compare the tensor
product object with `ModuleCat.extendScalars`.
(blueprint: new-residue-kernel-localized-cokernel-transport-aux)
Source: Mathlib.RingTheory.Localization.BaseChange and
Mathlib.Algebra.Module.LocalizedModule.Submodule.
-/
theorem localized_range_quotient_extendScalars_aux
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ e : LocalizedModule 𝔭.primeCompl (Y : Type v) ≃ₗ[Localization.AtPrime 𝔭]
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y : Type v),
      ((LinearMap.range f.hom).localized 𝔭.primeCompl).map e.toLinearMap =
        LinearMap.range ((ModuleCat.extendScalars
          (algebraMap R (Localization.AtPrime 𝔭))).map f).hom := by
  let A := Localization.AtPrime 𝔭
  let A₀ := (restrictScalars (algebraMap R A)).obj (of A A)
  let : Module A A₀ := inferInstanceAs (Module A A)
  have : IsScalarTower R A A₀ :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let t (Z : ModuleCat R) (a : A) (z : Z) :
      (extendScalars (algebraMap R A)).obj Z :=
    @TensorProduct.tmul R _ A₀ Z _ _ A₀.isModule _ a z
  let h : A ≃ₗ[R] A₀ :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; exact Algebra.smul_def r x }
  let e := LocalizedModule.equivTensorProduct 𝔭.primeCompl Y
  let e' : LocalizedModule 𝔭.primeCompl Y ≃ₗ[A]
      (ModuleCat.extendScalars (algebraMap R A)).obj Y := by
    exact (e.restrictScalars R ≪≫ₗ
      TensorProduct.congr h (LinearEquiv.refl R Y)).extendScalarsOfIsLocalization
        𝔭.primeCompl A
  refine ⟨e', ?_⟩
  change Submodule.map e'.toLinearMap
    ((f.hom.range).localized' (Localization.AtPrime 𝔭) 𝔭.primeCompl
      (LocalizedModule.mkLinearMap 𝔭.primeCompl Y)) = _
  rw [Submodule.localized'_eq_span]
  rw [Submodule.map_span]
  have he (y : Y) : e' (LocalizedModule.mk y 1) =
      t Y 1 y := by
    change (TensorProduct.congr h (LinearEquiv.refl R Y))
      (e (LocalizedModule.mk y 1)) = _
    rw [LocalizedModule.equivTensorProduct_apply_mk, Localization.mk_one,
      TensorProduct.congr_tmul]
    rfl
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, ⟨y, ⟨x, rfl⟩, rfl⟩, rfl⟩
    refine ⟨t X 1 x, ?_⟩
    change t Y 1 (f x) = e' (LocalizedModule.mk (f x) 1)
    exact (he (f x)).symm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      change A at a
      have hx : e' (LocalizedModule.mk (f x) 1) ∈
          Submodule.span A (e'.toLinearMap ''
            (LocalizedModule.mkLinearMap 𝔭.primeCompl Y '' (f.hom.range : Set Y))) :=
        Submodule.subset_span ⟨_, ⟨f x, ⟨x, rfl⟩, rfl⟩, rfl⟩
      rw [he] at hx
      change ((extendScalars (algebraMap R A)).map f)
        (t X a x) ∈ _
      rw [ExtendScalars.map_tmul]
      have hs := Submodule.smul_mem (R := A) _ (a : A) hx
      have ha : (show A from a) • (show A₀ from (1 : A)) = a := by
        exact @mul_one A _ a
      rw [TensorProduct.smul_tmul' (R' := A) (M := A₀), ha] at hs
      exact hs
    | add z w hz hw => simpa using Submodule.add_mem _ hz hw

/--
The quotient of a localized module by the localized range is the quotient of the
extension of scalars by the extended range, obtained by transporting the range
identification through `Submodule.Quotient.equiv`.
(blueprint: new-residue-kernel-localized-cokernel-transport)
-/
theorem localized_range_quotient_extendScalars
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    Nonempty ((LocalizedModule 𝔭.primeCompl Y ⧸
        (LinearMap.range f.hom).localized 𝔭.primeCompl) ≃ₗ[Localization.AtPrime 𝔭]
      (((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y)
        ⧸ LinearMap.range ((ModuleCat.extendScalars
          (algebraMap R (Localization.AtPrime 𝔭))).map f).hom)) := by
  obtain ⟨e, he⟩ := localized_range_quotient_extendScalars_aux R X Y f 𝔭
  exact ⟨Submodule.Quotient.equiv _ _ e he⟩

end ModuleCat
