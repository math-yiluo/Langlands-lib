/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section
set_option autoImplicit false
universe v
namespace ModuleCat

/-- Computing the kernel and cokernel of an actual diagonal normal form.

Source: Stacks Project, Tag 00O0, the kernel and cokernel computation after the
unit-minor operations. Proof: a vector is in the kernel precisely when its U
coordinate is zero and its last coordinate is in ker g. The source equivalence
therefore identifies ker g with ker f. Project the target along eY onto C/range g.
This map is onto, and its kernel consists precisely of vectors whose C coordinate
is g(a), hence precisely the image of f. The first isomorphism theorem finishes.
(blueprint: new-residue-kernel-unit-minor-quotient) -/
theorem residue_kernel_unit_minor_quotient
    (A : Type v) [CommRing A] (X Y U C : ModuleCat.{v} A)
    (f : X →ₗ[A] Y) (g : A →ₗ[A] C)
    (eX : X ≃ₗ[A] (U × A)) (eY : Y ≃ₗ[A] (U × C))
    (hdiag : ∀ x, eY (f x) = ((eX x).1, g (eX x).2)) :
    Nonempty (LinearMap.ker g ≃ₗ[A] LinearMap.ker f) ∧
      Nonempty ((Y ⧸ LinearMap.range f) ≃ₗ[A] (C ⧸ LinearMap.range g)) := by
  let k : LinearMap.ker g ≃ₗ[A] LinearMap.ker f :=
    { toFun := fun a ↦ ⟨eX.symm (0, a.val), by
        apply eY.injective
        simp [hdiag]⟩
      invFun := fun x ↦ ⟨(eX x.val).2, by
        have h := congrArg Prod.snd (hdiag x.val)
        simpa [LinearMap.mem_ker.mp x.property] using h.symm⟩
      left_inv := fun a ↦ by simp
      right_inv := fun x ↦ by
        apply Subtype.ext
        apply eX.injective
        have h := congrArg Prod.fst (hdiag x.val)
        have hzero : (eX x.val).1 = 0 := by
          simpa [LinearMap.mem_ker.mp x.property] using h.symm
        rw [eX.apply_symm_apply]
        exact Prod.ext hzero.symm rfl
      map_add' := fun a b ↦ by
        apply Subtype.ext
        simp [← map_add]
      map_smul' := fun r a ↦ by
        apply Subtype.ext
        simp [← map_smul] }
  let q : Y →ₗ[A] C ⧸ LinearMap.range g :=
    (LinearMap.range g).mkQ.comp ((LinearMap.snd A U C).comp eY.toLinearMap)
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨c, rfl⟩ := (LinearMap.range g).mkQ_surjective z
    exact ⟨eY.symm (0, c), by simp [q]⟩
  have hker : LinearMap.ker q = LinearMap.range f := by
    ext y
    change q y = 0 ↔ ∃ x, f x = y
    constructor
    · intro hy
      have hmem : (eY y).2 ∈ LinearMap.range g := by
        simpa [q] using hy
      obtain ⟨a, ha⟩ := hmem
      refine ⟨eX.symm ((eY y).1, a), ?_⟩
      apply eY.injective
      simp [hdiag, ha]
    · rintro ⟨x, rfl⟩
      simp [q, hdiag]
  exact ⟨⟨k⟩, ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    (q.quotKerEquivOfSurjective hq)⟩⟩

end ModuleCat
