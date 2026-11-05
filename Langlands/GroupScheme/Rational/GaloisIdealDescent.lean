import Langlands.GroupScheme.TensorGaloisPoint
import Langlands.LinearAlgebra.GaloisSubmoduleDescent
import Mathlib.RingTheory.Ideal.Maps

/-! # Infinite-Galois descent of tensor ideals -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.GaloisIdealDescent

open Langlands.LinearAlgebra.GaloisSubmoduleDescent

set_option backward.isDefEq.respectTransparency false

variable (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A]

/-- Contract a tensor ideal along the ground-algebra inclusion. -/
def groundIdeal (J : Ideal (K ⊗[k] A)) : Ideal A :=
  J.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom

theorem repr_includeRight {I : Type u} (b : Module.Basis I k A) (y : I →₀ k) :
    (b.baseChange K).repr
        ((Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) (b.repr.symm y)) =
      extend y := by
  ext i
  simp [Algebra.TensorProduct.includeRight_apply, Algebra.smul_def]

variable [IsGalois k K]

/-- A coefficient-stable ideal is extended from its contraction to the ground algebra. -/
theorem map_groundIdeal_eq (J : Ideal (K ⊗[k] A))
    (hJ : ∀ (σ : K ≃ₐ[k] K) (x : K ⊗[k] A),
      x ∈ J → TensorGaloisPoint.coefficientConjugate k K A σ x ∈ J) :
    (groundIdeal k K A J).map
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom = J := by
  classical
  apply le_antisymm
  · exact Ideal.map_comap_le
  · let b := Module.Free.chooseBasis k A
    let e := (b.baseChange K).repr
    let W := (J.restrictScalars K).comap e.symm.toLinearMap
    have hW : ∀ (σ : K ≃ₐ[k] K) (x : _ →₀ K),
        x ∈ W → conjugate σ x ∈ W := by
      intro σ x hx
      have he : e.symm (conjugate σ x) =
          TensorGaloisPoint.coefficientConjugate k K A σ (e.symm x) := by
        apply e.injective
        rw [LinearEquiv.apply_symm_apply]
        symm
        calc
          e (TensorGaloisPoint.coefficientConjugate k K A σ (e.symm x)) =
              conjugate σ (e (e.symm x)) := by
            ext i
            exact TensorGaloisPoint.repr_coefficientConjugate k K A b σ (e.symm x) i
          _ = conjugate σ x := by rw [LinearEquiv.apply_symm_apply]
      change e.symm (conjugate σ x) ∈ J
      rw [he]
      exact hJ σ _ hx
    have hspan : Submodule.span K {x | ∃ y : _ →₀ k, extend y = x ∧ x ∈ W} ≤
        (((groundIdeal k K A J).map
          (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom
            ).restrictScalars K).comap e.symm.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro x ⟨y, rfl, hy⟩
      have he : e.symm (extend y) =
          (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) (b.repr.symm y) :=
        e.injective (by simpa only [LinearEquiv.apply_symm_apply] using
          (repr_includeRight k K A b y).symm)
      change e.symm (extend y) ∈ (groundIdeal k K A J).map
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom
      rw [he]
      apply Ideal.mem_map_of_mem
      change (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
        (b.repr.symm y) ∈ J
      rw [← he]
      exact hy
    intro x hx
    have hxe : e x ∈ W := by
      change e.symm (e x) ∈ J
      simpa using hx
    rw [eq_span_ground_vectors W hW] at hxe
    simpa only [Submodule.mem_comap, LinearEquiv.coe_coe, Submodule.restrictScalars_mem,
      LinearEquiv.symm_apply_apply] using hspan hxe

/-- Maps agreeing on the ground algebra give equal extensions of a stable tensor ideal. -/
theorem map_eq_of_comp_includeRight_eq
    {B : Type u} [CommRing B] [Algebra k B]
    (J : Ideal (K ⊗[k] A))
    (hJ : ∀ (σ : K ≃ₐ[k] K) (x : K ⊗[k] A),
      x ∈ J → TensorGaloisPoint.coefficientConjugate k K A σ x ∈ J)
    (f g : K ⊗[k] A →ₐ[k] B)
    (hfg : f.comp Algebra.TensorProduct.includeRight =
      g.comp Algebra.TensorProduct.includeRight) :
    J.map f.toRingHom = J.map g.toRingHom := by
  rw [← map_groundIdeal_eq k K A J hJ, Ideal.map_map, Ideal.map_map]
  apply congrArg (fun h : A →+* B => (groundIdeal k K A J).map h)
  exact congrArg AlgHom.toRingHom hfg

end Langlands.GroupScheme.GaloisIdealDescent
