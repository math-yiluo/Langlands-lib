import Langlands.Global.RationalProfiniteIntegerComparison
import Langlands.Global.PrimeToFiniteAdeles

/-! # Normalized prime-to-modulus residue and finite-adele comparison -/

open scoped TensorProduct

namespace Langlands.Global

/-- The away scalar comparison, coupled to the witnesses chosen from the
explicit full comparison hypothesis. This proposition supplies no proof or
unconditional comparison map. -/
def PrimeToRationalProfiniteIntegerAdeleComparison
    (h : RationalProfiniteIntegerAdeleComparison) (m : ℕ) : Prop :=
  let eFull₀ := h.choose
  let eFull := h.choose_spec.2.2.2.choose
  ∃ e₀ : PrimeToProfiniteIntegerRing m ≃+* primeToIntegralFiniteAdeles m,
    Continuous e₀ ∧ Continuous e₀.symm ∧
      (∀ z : ℤ, (e₀ (PrimeToProfiniteIntegerRing.intCastHom m z) :
        PrimeToFiniteAdeles m) = algebraMap ℚ (PrimeToFiniteAdeles m) (z : ℚ)) ∧
      (∀ a : ProfiniteIntegerRing,
        e₀ (PrimeToProfiniteIntegerRing.restrict m a) =
          primeToIntegralRestriction m (eFull₀ a)) ∧
      ∃ e : (ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) ≃ₐ[ℚ] PrimeToFiniteAdeles m,
        (∀ (q : ℚ) (a : PrimeToProfiniteIntegerRing m),
          e (q ⊗ₜ[ℤ] a) = algebraMap ℚ (PrimeToFiniteAdeles m) q *
            (e₀ a : PrimeToFiniteAdeles m)) ∧
        (∀ (q : ℚ) (a : ProfiniteIntegerRing),
          e (q ⊗ₜ[ℤ] PrimeToProfiniteIntegerRing.restrict m a) =
            primeToFiniteRestriction m (eFull (q ⊗ₜ[ℤ] a)))

/-- Every natural excluded modulus admits the normalized away comparison,
compatible with the explicitly assumed full comparison. -/
def PrimeToRationalProfiniteIntegerAdeleComparisons : Prop :=
  ∀ (h : RationalProfiniteIntegerAdeleComparison) (m : ℕ),
    PrimeToRationalProfiniteIntegerAdeleComparison h m

end Langlands.Global
