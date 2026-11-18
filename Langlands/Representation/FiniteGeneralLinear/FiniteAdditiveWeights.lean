import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Matrix.Mul
import Mathlib.RepresentationTheory.Basic

/-! Finite additive weight projections and coordinates on the dual of a finite field vector space. -/

noncomputable section

open scoped BigOperators Matrix

namespace Langlands.FiniteGeneralLinear

section Rows

variable {k ι : Type*} [Field k] [Fintype ι]

/-- Pair a row with the column variable and apply an additive character of the field. -/
def rowCharacter (ψ : AddChar k ℂ) (a : ι → k) : AddChar (ι → k) ℂ where
  toFun x := ψ (a ⬝ᵥ x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [dotProduct_add, AddChar.map_add_eq_mul]

@[simp] theorem rowCharacter_apply (ψ : AddChar k ℂ) (a x : ι → k) :
    rowCharacter ψ a x = ψ (a ⬝ᵥ x) := rfl

/-- Over a finite field, a nontrivial character identifies the additive dual with the row space. -/
theorem rowCharacter_surjective [Finite k] {ψ : AddChar k ℂ} (hψ : ψ ≠ 0) :
    Function.Surjective (rowCharacter (ι := ι) ψ) := by
  classical
  let := Fintype.ofFinite (ι → k)
  refine ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨?_, AddChar.card_eq.symm⟩).2
  intro a b hab
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra! h
    exact hψ (DFunLike.ext _ _ h)
  funext i
  by_contra hi
  let x : ι → k := Pi.single i (t / (a i - b i))
  have he := DFunLike.congr_fun hab x
  simp only [rowCharacter_apply, x, dotProduct_single] at he
  have hdiff : a i * (t / (a i - b i)) - b i * (t / (a i - b i)) = t := by
    rw [← sub_mul, mul_div_cancel₀ t (sub_ne_zero.mpr hi)]
  apply ht
  rw [← hdiff, sub_eq_add_neg (a i * _) (b i * _), ψ.map_add_eq_mul, he,
    ← ψ.map_add_eq_mul, add_neg_cancel, ψ.map_zero_eq_one]

end Rows

section Weights

variable {A V : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup V] [Module ℂ V]

/-- An unnormalized additive character projector. -/
def additiveWeightSum (ρ : Representation ℂ (Multiplicative A) V) (χ : AddChar A ℂ)
    (v : V) : V :=
  ∑ x : A, χ (-x) • ρ (Multiplicative.ofAdd x) v

/-- The image of the sum transforms by its character. -/
theorem apply_additiveWeightSum (ρ : Representation ℂ (Multiplicative A) V)
    (χ : AddChar A ℂ) (v : V) (a : A) :
    ρ (Multiplicative.ofAdd a) (additiveWeightSum ρ χ v) = χ a • additiveWeightSum ρ χ v := by
  simp only [additiveWeightSum, map_sum, map_smul, ← Module.End.mul_apply, ← map_mul,
    ← ofAdd_add, Finset.smul_sum, smul_smul]
  apply Fintype.sum_equiv (Equiv.addLeft a)
  intro x
  change χ (-x) • ρ (Multiplicative.ofAdd (a + x)) v =
    (χ a * χ (-(a + x))) • ρ (Multiplicative.ofAdd (a + x)) v
  rw [← χ.map_add_eq_mul, show a + -(a + x) = -x by abel]

/-- Orthogonality of additive characters recovers the original vector from the projections. -/
theorem sum_additiveWeightSum (ρ : Representation ℂ (Multiplicative A) V) (v : V) :
    ∑ χ : AddChar A ℂ, additiveWeightSum ρ χ v = (Fintype.card A : ℂ) • v := by
  classical
  simp only [additiveWeightSum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero, ite_smul, zero_smul]
  rw [Finset.sum_eq_single (0 : A)]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

end Weights

end Langlands.FiniteGeneralLinear
