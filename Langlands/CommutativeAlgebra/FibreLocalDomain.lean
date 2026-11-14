import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.Ideal

/-! # Regular elements of fibre local rings from a domain fibre

Let `R` be an `A`-algebra, `P` a prime of `R` and `p = P ∩ A`. If the fibre ring `κ(p) ⊗ R` is a
domain and `1 ⊗ s ≠ 0` there, then `s` is a nonzerodivisor of the fibre local ring `R_P ⧸ p R_P`.
-/

universe u

open TensorProduct Algebra.TensorProduct

namespace Langlands.CommutativeAlgebra.FibreLocalDomain

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] (P : Ideal R) [P.IsPrime]

/-- The prime of the fibre ring corresponding to `P`. -/
lemma exists_fiber_prime :
    ∃ q : Ideal ((P.comap (algebraMap A R)).Fiber R), q.IsPrime ∧
      q.comap (includeRight (R := A) (A := (P.comap (algebraMap A R)).ResidueField)
        (B := R)).toRingHom = P := by
  let p := P.comap (algebraMap A R)
  have hP : P ∈ p.primesOver R := ⟨inferInstance, ⟨rfl⟩⟩
  let q := PrimeSpectrum.primesOverOrderIsoFiber A R p ⟨P, hP⟩
  refine ⟨q.asIdeal, q.2, ?_⟩
  have h := (PrimeSpectrum.primesOverOrderIsoFiber A R p).symm_apply_apply ⟨P, hP⟩
  exact congrArg Subtype.val h

/-- **Fibre domain criterion.** -/
theorem isSMulRegular_of_isDomain_fiber (s : R)
    (hdom : IsDomain ((P.comap (algebraMap A R)).Fiber R))
    (hs : (1 : (P.comap (algebraMap A R)).ResidueField) ⊗ₜ[A] s ≠ 0) :
    IsSMulRegular (Localization.AtPrime P ⧸
        (P.comap (algebraMap A R)).map (algebraMap A (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P) s) := by
  set p := P.comap (algebraMap A R) with hp
  obtain ⟨q, hqp, hq⟩ := exists_fiber_prime (A := A) P
  -- the fibre local ring is a domain
  have hloc : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors q)
  have e := Ideal.Fiber.algEquivAux₂ p q
  have hD₀ := e.symm.toMulEquiv.isDomain
  have hq' : Ideal.comap (includeRight (R := A) (A := p.ResidueField) (B := R)) q = P :=
    hq
  have key : ∀ (r : Ideal R) [r.IsPrime], r = P →
      IsDomain (Localization.AtPrime r ⧸
        (p.map (algebraMap A R)).map (algebraMap R (Localization.AtPrime r))) →
      IsDomain (Localization.AtPrime P ⧸
        (p.map (algebraMap A R)).map (algebraMap R (Localization.AtPrime P))) := by
    rintro r _ rfl h
    exact h
  have hD₁ := key _ hq' hD₀
  have hI : (p.map (algebraMap A R)).map (algebraMap R (Localization.AtPrime P)) =
      p.map (algebraMap A (Localization.AtPrime P)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [hI] at hD₁
  -- the image of `s` is nonzero
  have hne : Ideal.Quotient.mk (p.map (algebraMap A (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P) s) ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hI,
      IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl] at h0
    obtain ⟨m, hm, hms⟩ := h0
    have hker : p.map (algebraMap A R) ≤
        RingHom.ker (includeRight (R := A) (A := p.ResidueField) (B := R)).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change includeRight (algebraMap A R a) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
        Ideal.algebraMap_residueField_eq_zero.mpr ha, TensorProduct.zero_tmul]
    have h1 := hker hms
    rw [RingHom.mem_ker, map_mul] at h1
    have h2 : (includeRight (R := A) (A := p.ResidueField) (B := R)) m = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hs
    apply hm
    rw [← hq]
    change (includeRight (R := A) (A := p.ResidueField) (B := R)) m ∈ q
    rw [h2]
    exact q.zero_mem
  intro x y hxy
  change algebraMap R (Localization.AtPrime P) s • x = algebraMap R (Localization.AtPrime P) s • y
    at hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : ∀ c, algebraMap R (Localization.AtPrime P) s •
      Ideal.Quotient.mk (p.map (algebraMap A (Localization.AtPrime P))) c =
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) s) * Ideal.Quotient.mk _ c :=
    fun c => by rw [← map_mul]; rfl
  rw [h1, h1] at hxy
  exact mul_left_cancel₀ hne hxy

end Langlands.CommutativeAlgebra.FibreLocalDomain
