import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Basic

/-! # Scalars transported along a Galois orbit -/

noncomputable section

universe u v

namespace Langlands.LinearAlgebra.GaloisOrbitScalars

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X : Type v} [AddCommGroup X]
  (r : Representation ℤ (K ≃ₐ[k] K) X) (χ : X)

/-- Transport a scalar from the chosen center along an orbit, and use zero outside it. -/
def orbitValue (a : K) (ψ : X) : K := by
  classical
  exact if h : ∃ σ : K ≃ₐ[k] K, r σ χ = ψ then h.choose a else 0

variable (H : Subgroup (K ≃ₐ[k] K))
  (hH : ∀ σ : K ≃ₐ[k] K, σ ∈ H ↔ r σ χ = χ)

include hH

/-- An element fixed by the stabilizer has an unambiguous transported scalar. -/
theorem orbitValue_apply (a : IntermediateField.fixedField H) (σ : K ≃ₐ[k] K) :
    orbitValue r χ (a : K) (r σ χ) = σ (a : K) := by
  classical
  have hex : ∃ τ : K ≃ₐ[k] K, r τ χ = r σ χ := ⟨σ, rfl⟩
  rw [orbitValue, dite_eq_left hex]
  let τ : K ≃ₐ[k] K := hex.choose
  have hτ : r τ χ = r σ χ := hex.choose_spec
  have hmem : τ⁻¹ * σ ∈ H := by
    apply (hH _).mpr
    rw [map_mul, Module.End.mul_apply, ← hτ, Representation.inv_self_apply]
  have ha : (τ⁻¹ * σ) (a : K) = a :=
    (IntermediateField.mem_fixedField_iff H (a : K)).mp a.property _ hmem
  have hh := congrArg τ ha
  change τ (τ.symm (σ (a : K))) = τ (a : K) at hh
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh.symm

/-- Transported scalars are Galois equivariant on the whole orbit. -/
theorem orbitValue_equivariant (a : IntermediateField.fixedField H)
    (σ : K ≃ₐ[k] K) (ψ : X)
    (hψ : ψ ∈ Set.range (fun τ : K ≃ₐ[k] K => r τ χ)) :
    orbitValue r χ (a : K) (r σ ψ) = σ (orbitValue r χ (a : K) ψ) := by
  obtain ⟨τ, rfl⟩ := hψ
  have hcomp : r σ (r τ χ) = r (σ * τ) χ := by
    rw [map_mul, Module.End.mul_apply]
  rw [hcomp, orbitValue_apply r χ H hH, orbitValue_apply r χ H hH]
  rfl

end Langlands.LinearAlgebra.GaloisOrbitScalars
