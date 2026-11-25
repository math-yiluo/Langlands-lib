/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Algebra.Homology.ResidueKernelUnitMinorPivot
@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

-- Gaussian elimination uses only the invertibility of the leading block.
private theorem normalize_pivot
    (A : Type v) [CommRing A] (U C : ModuleCat.{v} A)
    (F : (U × A) →ₗ[A] (U × C)) (B : U ≃ₗ[A] U)
    (hB : ∀ u, (F (u, 0)).1 = B u) :
    ∃ (g : A →ₗ[A] C) (sX : (U × A) ≃ₗ[A] (U × A))
      (sY : (U × C) ≃ₗ[A] (U × C)),
      ∀ p, sY (F p) = ((sX p).1, g (sX p).2) := by
  let b : A →ₗ[A] U := (LinearMap.fst A U C).comp (F.comp (LinearMap.inr A U A))
  let c : U →ₗ[A] C := (LinearMap.snd A U C).comp (F.comp (LinearMap.inl A U A))
  let d : A →ₗ[A] C := (LinearMap.snd A U C).comp (F.comp (LinearMap.inr A U A))
  have hF (u : U) (a : A) : F (u, a) = (B u + b a, c u + d a) := by
    have hp : (u, a) = (u, 0) + (0, a) := by simp
    rw [hp, F.map_add]
    apply Prod.ext
    · exact congrArg (fun z ↦ z + (F (0, a)).1) (hB u)
    · rfl
  let sX : (U × A) ≃ₗ[A] (U × A) :=
    { toFun := fun p ↦ (B p.1 + b p.2, p.2)
      invFun := fun p ↦ (B.symm (p.1 - b p.2), p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      map_add' := by intro p q; simp; abel
      map_smul' := by intro a p; simp [smul_add, -smul_eq_mul] }
  let sY : (U × C) ≃ₗ[A] (U × C) :=
    { toFun := fun p ↦ (p.1, p.2 - c (B.symm p.1))
      invFun := fun p ↦ (p.1, p.2 + c (B.symm p.1))
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      map_add' := by intro p q; simp; abel
      map_smul' := by intro a p; simp [smul_sub] }
  let g : A →ₗ[A] C := d - c.comp (B.symm.toLinearMap.comp b)
  refine ⟨g, sX, sY, ?_⟩
  rintro ⟨u, a⟩
  rw [hF]
  apply Prod.ext
  · rfl
  · change c u + d a - c (B.symm (B u + b a)) = d a - c (B.symm (b a))
    simp only [map_add, B.symm_apply_apply]
    abel

/--
(blueprint: new-residue-kernel-unit-minor-matrix-core)
Matrix unit-minor normalization over a local ring, assuming the localized modules are free.
Source: Stacks Project, Tags 00O0 and 00NX, matrix unit-minor argument.
The proof chooses a maximal nonzero residue minor and performs elementary row
and column operations. -/
theorem residue_kernel_unit_minor_matrix_core
    (R : Type v) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [IsLocalRing A] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (hX : Module.Free A
      ((ModuleCat.extendScalars (algebraMap R A)).obj X))
    (hY : Module.Free A ((ModuleCat.extendScalars (algebraMap R A)).obj Y))
    (hfX : Module.Finite A ((ModuleCat.extendScalars (algebraMap R A)).obj X))
    (hfY : Module.Finite A ((ModuleCat.extendScalars (algebraMap R A)).obj Y))
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars
      ((IsLocalRing.residue A).comp (algebraMap R A))).map f).hom
      ≃ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A)) :
    ∃ (U C : ModuleCat.{v} A) (g : A →ₗ[A] C), Module.Free A C ∧
      ∃ (eX : ((ModuleCat.extendScalars (algebraMap R A)).obj X)
          ≃ₗ[A] (U × A)) (eY : ((ModuleCat.extendScalars (algebraMap R A)).obj Y)
          ≃ₗ[A] (U × C)),
        ∀ x, eY (((ModuleCat.extendScalars (algebraMap R A)).map f).hom x) =
          ((eX x).1, g (eX x).2) := by
  obtain ⟨U, C, hC, eX, eY, B, hB⟩ :=
    residue_kernel_unit_minor_pivot R A X Y f hX hY hfX hfY hres
  let F := eY.toLinearMap.comp
    (((ModuleCat.extendScalars (algebraMap R A)).map f).hom.comp eX.symm.toLinearMap)
  obtain ⟨g, sX, sY, hform⟩ := normalize_pivot A U C F B hB
  refine ⟨U, C, g, hC, eX.trans sX, eY.trans sY, ?_⟩
  intro x
  simpa only [LinearEquiv.trans_apply, F, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hform (eX x)
end ModuleCat
