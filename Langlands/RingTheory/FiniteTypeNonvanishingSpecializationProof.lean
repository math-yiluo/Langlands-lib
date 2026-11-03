import Langlands.RingTheory.FiniteTypeNonvanishingSpecializationStatement
import Mathlib.RingTheory.Jacobson.Ring

/-! # Proof of finite-type specialization with prescribed nonvanishing -/

noncomputable section

universe u v

namespace Langlands.RingTheory

open scoped BigOperators

/-- A finite-type algebra over an algebraically closed field has a ground-field
specialization preserving any finite product which is not nilpotent. -/
theorem finiteTypeNonvanishingSpecialization :
    FiniteTypeNonvanishingSpecializationStatement.{u,v} := by
  classical
  intro k _ _ A _ _ _ s hs
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hp : (∏ a ∈ s, a) ∉ (⊥ : Ideal A).jacobson := by
    rw [← Ideal.radical_eq_jacobson, Ideal.mem_radical_iff]
    simpa only [Ideal.mem_bot, IsNilpotent] using hs
  obtain ⟨m, hm, hpm⟩ :
      ∃ m : Ideal A, m.IsMaximal ∧ (∏ a ∈ s, a) ∉ m := by
    by_contra! hm
    apply hp
    rw [Ideal.jacobson, Ideal.mem_sInf]
    exact fun J hJ ↦ hm J hJ.2
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite k (A ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let ψ : (A ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  let φ : A →ₐ[k] k := ψ.comp (Ideal.Quotient.mkₐ k m)
  refine ⟨φ, ?_⟩
  have hφ : φ (∏ a ∈ s, a) ≠ 0 := by
    intro h
    apply hpm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply ψ.injective
    change ψ ((Ideal.Quotient.mkₐ k m) (∏ a ∈ s, a)) = ψ 0
    change ψ ((Ideal.Quotient.mkₐ k m) (∏ a ∈ s, a)) = 0 at h
    simpa only [map_zero] using h
  have hprod : (∏ a ∈ s, φ a) ≠ 0 := by
    simpa only [map_prod] using hφ
  exact Finset.prod_ne_zero_iff.mp hprod

end Langlands.RingTheory
