import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Frobenius approximation on finite sets in algebraic extensions -/

noncomputable section

universe u v

namespace Langlands.FieldTheory

variable (k : Type u) [Field k] [Fintype k]
    (K : Type v) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/-- Every automorphism agrees with a nonnegative power of arithmetic Frobenius
on any prescribed finite set of elements of an algebraic extension. -/
theorem exists_frobenius_pow_eq_on_finset (σ : K ≃ₐ[k] K) (s : Finset K) :
    ∃ n : ℕ, ∀ x ∈ s,
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ n) x = σ x := by
  classical
  let L := IntermediateField.adjoin k (s : Set K)
  let : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let : Finite L := Module.finite_of_finite k
  let : IsGalois k L := inferInstance
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).surjective
      (AlgEquiv.restrictNormalHom L σ)
  refine ⟨n.val, ?_⟩
  intro x hx
  let y : L := ⟨x, IntermediateField.subset_adjoin k (s : Set K) hx⟩
  have h := congrArg (fun z : L => (z : K)) (AlgEquiv.congr_fun hn y)
  simpa only [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    IntermediateField.coe_pow, AlgEquiv.restrictNormalHom_apply] using h

/-- Choose an exponent whose Frobenius power agrees with `σ` on `s`. -/
def frobeniusApproximationExponent (σ : K ≃ₐ[k] K) (s : Finset K) : ℕ :=
  (exists_frobenius_pow_eq_on_finset k K σ s).choose

theorem frobeniusApproximationExponent_spec (σ : K ≃ₐ[k] K) (s : Finset K)
    (x : K) (hx : x ∈ s) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^
      frobeniusApproximationExponent k K σ s) x = σ x :=
  (exists_frobenius_pow_eq_on_finset k K σ s).choose_spec x hx

end Langlands.FieldTheory
