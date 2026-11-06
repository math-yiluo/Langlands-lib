import Langlands.GroupScheme.Reductive.SteinbergMonomialBox
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Coordinate translations and Steinberg monomial boxes -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.SteinbergTranslationBox

variable {k : Type u} [Field k]

section CoefficientExtraction

variable {A : Type w} [CommRing A] [Algebra k A]

/-- A subspace containing all scalar-parameter values of a polynomial contains
its coefficients over an infinite field. -/
theorem coeff_mem_of_eval_algebraMap_mem [Infinite k]
    (P : Polynomial A) (W : Submodule k A)
    (hP : ∀ t : k, P.eval (algebraMap k A t) ∈ W) (n : ℕ) :
    P.coeff n ∈ W := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W (P.coeff n)).mp
  intro f hf
  let Q : Polynomial k :=
    Polynomial.ofFinsupp
      (AddMonoidAlgebra.ofCoeff (P.toFinsupp.coeff.mapRange f f.map_zero))
  have heval (t : k) :
      Q.eval t = f (P.eval (algebraMap k A t)) := by
    change (Polynomial.ofFinsupp
      (AddMonoidAlgebra.ofCoeff
        (P.toFinsupp.coeff.mapRange f f.map_zero))).eval t = _
    clear hP Q
    induction P using Polynomial.induction_on' with
    | add P₁ P₂ h₁ h₂ =>
      simp only [Polynomial.toFinsupp_add, AddMonoidAlgebra.coeff_add,
        Finsupp.mapRange_add f.map_add, AddMonoidAlgebra.ofCoeff_add,
        Polynomial.ofFinsupp_add, Polynomial.eval_add, map_add, h₁, h₂]
    | monomial m a =>
      simp only [Polynomial.toFinsupp_monomial, AddMonoidAlgebra.coeff_single,
        Finsupp.mapRange_single, AddMonoidAlgebra.ofCoeff_single,
        Polynomial.ofFinsupp_single, Polynomial.eval_monomial, ← map_pow]
      rw [mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hQ : Q = 0 := Polynomial.funext fun t => by
    rw [heval, Polynomial.eval_zero]
    exact (Submodule.mem_dualAnnihilator f).mp hf _ (hP t)
  have h := congrArg (fun q : Polynomial k => q.coeff n) hQ
  exact h

end CoefficientExtraction

open MvPolynomial

variable {σ : Type v}

/-- Actual polynomial substitution translating one coordinate by a scalar. -/
def axisTranslation (i : σ) (t : k) :
    Module.End k (MvPolynomial σ k) := by
  classical
  exact (MvPolynomial.aeval
    (Function.update (MvPolynomial.X : σ → MvPolynomial σ k) i
      (MvPolynomial.X i + MvPolynomial.C t))).toLinearMap

theorem axisTranslation_monomial_one (i : σ) (t : k) (b : σ →₀ ℕ) :
    axisTranslation i t (monomial b (1 : k)) =
      monomial (b.erase i) 1 * (X i + C t) ^ b i := by
  classical
  have hb : b.erase i + Finsupp.single i (b i) = b := by
    ext j
    by_cases hji : j = i <;> simp [hji]
  have hm : monomial b (1 : k) = monomial (b.erase i) 1 * X i ^ b i := by
    rw [← monomial_add_single, hb]
  have he : MvPolynomial.aeval
      (Function.update (X : σ → MvPolynomial σ k) i (X i + C t))
      (monomial (b.erase i) (1 : k)) = monomial (b.erase i) 1 := by
    rw [aeval_monomial, map_one, one_mul, monomial_eq, map_one, one_mul]
    apply Finsupp.prod_congr
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      simp at hj
    simp only [Function.update_of_ne hji]
  change MvPolynomial.aeval _ (monomial b (1 : k)) = _
  rw [hm, map_mul, map_pow, aeval_X, Function.update_self]
  exact congrArg (fun P : MvPolynomial σ k => P * (X i + C t) ^ b i) he

/-- The genuine one-parameter polynomial family of coordinate translates
of a monomial. -/
def axisMonomialFamily (i : σ) (b : σ →₀ ℕ) :
    Polynomial (MvPolynomial σ k) :=
  Polynomial.C (monomial (b.erase i) 1) *
    (Polynomial.X + Polynomial.C (X i)) ^ b i

theorem axisMonomialFamily_eval (i : σ) (b : σ →₀ ℕ) (t : k) :
    (axisMonomialFamily (k := k) i b).eval (C t) =
      axisTranslation i t (monomial b 1) := by
  rw [axisTranslation_monomial_one, axisMonomialFamily,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, add_comm (C t)]

theorem axisMonomialFamily_coeff (i : σ) (b : σ →₀ ℕ) (n : ℕ) :
    (axisMonomialFamily (k := k) i b).coeff n =
      monomial (b - Finsupp.single i n) ((b i).choose n : k) := by
  classical
  have hb : b.erase i + Finsupp.single i (b i - n) =
      b - Finsupp.single i n := by
    ext j
    by_cases hji : j = i <;> simp [hji]
  rw [axisMonomialFamily, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow,
    ← mul_assoc, ← monomial_add_single, hb]
  rw [← C_eq_coe_nat, mul_comm, C_mul_monomial, mul_one]

/-- Stability under actual coordinate translations recovers the corresponding
binomial coefficient of each monomial in the subspace. -/
theorem monomial_binomial_mem_of_axisTranslation_mem [Infinite k]
    (W : Submodule k (MvPolynomial σ k))
    (hW : ∀ (i : σ) (t : k) (P : MvPolynomial σ k),
      P ∈ W → axisTranslation i t P ∈ W)
    (i : σ) (b : σ →₀ ℕ) (hb : monomial b 1 ∈ W) (n : ℕ) :
    monomial (b - Finsupp.single i n) ((b i).choose n : k) ∈ W := by
  rw [← axisMonomialFamily_coeff]
  apply coeff_mem_of_eval_algebraMap_mem
  intro t
  change (axisMonomialFamily (k := k) i b).eval (C t) ∈ W
  rw [axisMonomialFamily_eval]
  exact hW i t _ hb

/-- Lower each coordinate once, using a coefficient of its actual family
of translates. The other lowering coordinates remain unchanged. -/
theorem monomial_sub_mem_of_axisTranslation_mem [Infinite k]
    (N : σ →₀ ℕ) (W : Submodule k (MvPolynomial σ k))
    (hchoose : ∀ (i : σ) (n : ℕ), n ≤ N i → ((N i).choose n : k) ≠ 0)
    (hW : ∀ (i : σ) (t : k) (P : MvPolynomial σ k),
      P ∈ W → axisTranslation i t P ∈ W)
    (htop : monomial N 1 ∈ W)
    (a : σ →₀ ℕ) (ha : a ≤ N) :
    monomial (N - a) 1 ∈ W := by
  classical
  revert ha
  induction a using Finsupp.induction with
  | zero =>
    intro _
    simpa only [tsub_zero] using htop
  | single_add i n a hia _ ih =>
    intro ha
    have hai : a i = 0 := Finsupp.notMem_support_iff.mp hia
    have haN : a ≤ N := by
      intro j
      exact (Nat.le_add_left (a j) ((Finsupp.single i n) j)).trans (ha j)
    have hnN : n ≤ N i := by
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same, hai, add_zero] using ha i
    have hNi : (N - a) i = N i := by simp only [Finsupp.tsub_apply, hai, tsub_zero]
    have hcoeff : (((N - a) i).choose n : k) ≠ 0 := by
      rw [hNi]
      exact hchoose i n hnN
    have h := W.smul_mem (((N - a) i).choose n : k)⁻¹
      (monomial_binomial_mem_of_axisTranslation_mem W hW i (N - a) (ih haN) n)
    have hsub : N - a - Finsupp.single i n = N - (Finsupp.single i n + a) := by
      ext j
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Nat.sub_sub, add_comm]
    simpa only [hsub, smul_monomial, smul_eq_mul, inv_mul_cancel₀ hcoeff] using h

/-- Nonzero top-row binomial coefficients and translation stability recover
the entire lower monomial box from its top monomial. -/
theorem monomialBox_le_of_axisTranslation_mem [Infinite k]
    (N : σ →₀ ℕ) (W : Submodule k (MvPolynomial σ k))
    (hchoose : ∀ (i : σ) (n : ℕ), n ≤ N i → ((N i).choose n : k) ≠ 0)
    (hW : ∀ (i : σ) (t : k) (P : MvPolynomial σ k),
      P ∈ W → axisTranslation i t P ∈ W)
    (htop : monomial N 1 ∈ W) :
    SteinbergMonomialBox.monomialBox (k := k) N ≤ W := by
  rw [SteinbergMonomialBox.monomialBox, restrictSupport_eq_span, Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  change monomial m (1 : k) ∈ W
  have h := monomial_sub_mem_of_axisTranslation_mem N W hchoose hW htop
    (N - m) tsub_le_self
  have hsub : N - (N - m) = m := by
    ext i
    exact Nat.sub_sub_self (hm i)
  simpa only [hsub] using h

/-- Steinberg exponents supply all nonzero coefficients needed for generation
by actual coordinate translations over an infinite field. -/
theorem monomialBox_le_of_steinberg_axisTranslation_mem [Infinite k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ) (N : σ →₀ ℕ)
    (hN : ∀ i ∈ N.support, N i = p ^ r - 1)
    (W : Submodule k (MvPolynomial σ k))
    (hW : ∀ (i : σ) (t : k) (P : MvPolynomial σ k),
      P ∈ W → axisTranslation i t P ∈ W)
    (htop : monomial N 1 ∈ W) :
    SteinbergMonomialBox.monomialBox (k := k) N ≤ W := by
  apply monomialBox_le_of_axisTranslation_mem N W _ hW htop
  intro i n hn
  by_cases hi : i ∈ N.support
  · rw [hN i hi]
    exact RankOneSteinberg.choose_steinberg_cast_ne_zero p r n
      (by simpa only [hN i hi] using hn)
  · have hNi : N i = 0 := Finsupp.notMem_support_iff.mp hi
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero (by simpa only [hNi] using hn)
    simp only [hn0, Nat.choose_zero_right, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true]

/-- A finite space with a translation-stable polynomial image containing the
Steinberg top monomial has dimension at least the whole lower-box dimension. -/
theorem product_le_finrank_of_steinberg_axisTranslation_mem_range [Infinite k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ) (N : σ →₀ ℕ)
    (hN : ∀ i ∈ N.support, N i = p ^ r - 1)
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (L : V →ₗ[k] MvPolynomial σ k)
    (hL : ∀ (i : σ) (t : k) (P : MvPolynomial σ k),
      P ∈ LinearMap.range L → axisTranslation i t P ∈ LinearMap.range L)
    (htop : monomial N 1 ∈ LinearMap.range L) :
    (∏ i ∈ N.support, (N i + 1)) ≤ Module.finrank k V := by
  have hle := monomialBox_le_of_steinberg_axisTranslation_mem p r N hN
    (LinearMap.range L) hL htop
  rw [← SteinbergMonomialBox.finrank_monomialBox (k := k) N]
  exact (LinearMap.finrank_le_finrank_of_injective
    (Submodule.inclusion_injective hle)).trans (LinearMap.finrank_range_le L)

end Langlands.GroupScheme.SteinbergTranslationBox
