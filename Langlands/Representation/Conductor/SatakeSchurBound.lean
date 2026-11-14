import Langlands.Representation.Whittaker.Spherical
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Sym.Card

/-!
# Exponential bounds for the values of the spherical Whittaker function

The torus values `δ^(1/2)(ϖ^λ) s_λ(x)` of the spherical Whittaker function grow at most
exponentially in `∑ |λ_i|`. The Schur function is the Jacobi–Trudi determinant of the
complete homogeneous symmetric polynomials; each `h_k(x)` is a sum of at most
`2^(m+k)` monomials of degree `k`.
-/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial Langlands.Whittaker Langlands.GeneralLinear.Spherical

/-- A product of a multiset of values of norm at most `M` has norm at most `M^card`. -/
theorem norm_multiset_prod_map_le {ι : Type*} (s : Multiset ι) (f : ι → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i, ‖f i‖ ≤ M) : ‖(s.map f).prod‖ ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    calc
      ‖f a‖ * ‖(s.map f).prod‖ ≤ M * M ^ Multiset.card s :=
        mul_le_mul (h a) ih (norm_nonneg _) hM
      _ = M ^ Multiset.card s * M := mul_comm _ _

/-- `|h_k(x)| ≤ 2^(m+k) M^k` when every coordinate has norm at most `M`. -/
theorem norm_eval_hsymm_le {m : ℕ} (x : Fin m → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hx : ∀ i, ‖x i‖ ≤ M) (k : ℕ) :
    ‖eval x (hsymm (Fin m) ℂ k)‖ ≤ 2 ^ (m + k) * M ^ k := by
  classical
  have heval : eval x (hsymm (Fin m) ℂ k) = ∑ s : Sym (Fin m) k, (s.1.map x).prod := by
    rw [hsymm, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro i _
    simp
  rw [heval]
  calc
    ‖∑ s : Sym (Fin m) k, (s.1.map x).prod‖ ≤ ∑ s : Sym (Fin m) k, ‖(s.1.map x).prod‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _s : Sym (Fin m) k, M ^ k := by
      apply Finset.sum_le_sum
      intro s _
      have := norm_multiset_prod_map_le s.1 x hM hx
      rwa [s.2] at this
    _ = (Fintype.card (Sym (Fin m) k) : ℝ) * M ^ k := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ (m + k) * M ^ k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM k)
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      have h1 := Nat.choose_le_two_pow (m + k - 1) k
      have h2 : 2 ^ (m + k - 1) ≤ 2 ^ (m + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast le_trans h1 h2

/-- The completed bound for `completeSymm` with an integral index at most `N`. -/
theorem norm_eval_completeSymm_le {m : ℕ} (x : Fin m → ℂ) {M : ℝ} (hM : 1 ≤ M)
    (hx : ∀ i, ‖x i‖ ≤ M) {N : ℕ} {k : ℤ} (hk : k ≤ N) :
    ‖eval x (completeSymm (Fin m) ℂ k)‖ ≤ 2 ^ (m + N) * M ^ N := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  unfold completeSymm
  split_ifs with h0
  · refine le_trans (norm_eval_hsymm_le x hM0 hx k.toNat) ?_
    have hkN : k.toNat ≤ N := by omega
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
      (pow_le_pow_right₀ hM hkN) (pow_nonneg hM0 _) (by positivity)
  · simp only [map_zero, norm_zero]
    positivity

/-- **Exponential bound for the Satake–Schur values.** -/
theorem exists_satakeSchur_bound (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (x : Fin (n + 1) → ℂˣ) :
    ∃ C B : ℝ, 0 < C ∧ 1 ≤ B ∧ ∀ lam : Fin (n + 1) → ℤ,
      ‖halfModulus q lam * satakeSchur x lam‖ ≤ C * B ^ (∑ i, (lam i).natAbs) := by
  classical
  -- coordinate bound
  let M : ℝ := 1 + ∑ i, ‖(x i : ℂ)‖
  have hM : 1 ≤ M := by
    have : 0 ≤ ∑ i, ‖(x i : ℂ)‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  have hxM : ∀ i, ‖(x i : ℂ)‖ ≤ M := by
    intro i
    have := Finset.single_le_sum (f := fun i => ‖(x i : ℂ)‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  -- the determinant prefactor
  let P : ℝ := ‖∏ i, (x i : ℂ)‖ + ‖(∏ i, (x i : ℂ))⁻¹‖ + 1
  have hP : 1 ≤ P := by
    have := norm_nonneg (∏ i, (x i : ℂ))
    have := norm_nonneg ((∏ i, (x i : ℂ))⁻¹)
    simp only [P]
    linarith
  have hPa : ‖∏ i, (x i : ℂ)‖ ≤ P := by
    have := norm_nonneg ((∏ i, (x i : ℂ))⁻¹)
    simp only [P]
    linarith
  have hPb : ‖(∏ i, (x i : ℂ))⁻¹‖ ≤ P := by
    have := norm_nonneg (∏ i, (x i : ℂ))
    simp only [P]
    linarith
  have hprod : ∀ e : ℤ, ‖(∏ i, (x i : ℂ)) ^ e‖ ≤ P ^ e.natAbs := by
    intro e
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg e
    · rw [zpow_natCast, norm_pow, Int.natAbs_natCast]
      exact pow_le_pow_left₀ (norm_nonneg _) hPa _
    · rw [zpow_neg, zpow_natCast, ← inv_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
      exact pow_le_pow_left₀ (norm_nonneg _) hPb _
  -- the half modulus
  let Q : ℝ := Real.sqrt q
  have hQ : 1 ≤ Q := by
    simp only [Q]
    rw [Real.one_le_sqrt]
    exact_mod_cast hq
  have hhalf : ∀ lam : Fin (n + 1) → ℤ,
      ‖halfModulus q lam‖ ≤ Q ^ ((n + 1) * ∑ i, (lam i).natAbs) := by
    intro lam
    set e : ℤ := -∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i
    have he : e.natAbs ≤ (n + 1) * ∑ i, (lam i).natAbs := by
      have h1 : e.natAbs ≤ ∑ i : Fin (n + 1), (((n : ℤ) - 2 * (i : ℤ)) * lam i).natAbs := by
        simp only [e, Int.natAbs_neg]
        exact Int.natAbs_sum_le _ _
      refine le_trans h1 ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [Int.natAbs_mul]
      apply Nat.mul_le_mul_right
      have hi := i.isLt
      omega
    unfold halfModulus
    rw [norm_zpow]
    have hQn : ‖((Real.sqrt q : ℝ) : ℂ)‖ = Q := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [hQn]
    calc
      Q ^ e ≤ Q ^ (e.natAbs : ℤ) :=
        zpow_le_zpow_right₀ hQ (Int.le_natAbs)
      _ = Q ^ e.natAbs := zpow_natCast _ _
      _ ≤ Q ^ ((n + 1) * ∑ i, (lam i).natAbs) := pow_le_pow_right₀ hQ he
  -- the Jacobi–Trudi determinant
  have hdet : ∀ lam : Fin (n + 1) → ℤ,
      ‖eval (fun i => (x i : ℂ)) (jacobiTrudi ℂ fun i => lam i - lam (Fin.last n))‖ ≤
        (n + 1).factorial *
          (2 ^ ((n + 1) + (2 * ∑ i, (lam i).natAbs + (n + 1))) *
            M ^ (2 * ∑ i, (lam i).natAbs + (n + 1))) ^ (n + 1) := by
    intro lam
    set S := ∑ i, (lam i).natAbs
    have hS : ∀ i, (lam i).natAbs ≤ S := fun i =>
      Finset.single_le_sum (f := fun i => (lam i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    unfold jacobiTrudi
    rw [RingHom.map_det]
    refine le_trans (Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ)
      (x := 2 ^ ((n + 1) + (2 * S + (n + 1))) * M ^ (2 * S + (n + 1))) ?_) ?_
    · intro i j
      simp only [NormedField.toAbsoluteValue_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.of_apply]
      apply norm_eval_completeSymm_le _ hM hxM
      have h1 := hS i
      have h2 := hS (Fin.last n)
      have hj := j.isLt
      have hi := i.isLt
      omega
    · simp only [Fintype.card_fin, nsmul_eq_mul, le_refl]
  -- assemble
  refine ⟨(n + 1).factorial * (2 ^ ((n + 1) + (n + 1)) * M ^ (n + 1)) ^ (n + 1),
    Q ^ (n + 1) * P * (2 * M) ^ (2 * (n + 1)), by positivity, ?_, ?_⟩
  · have h4 : 1 ≤ (2 : ℝ) * M := by linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ) hP)
      (one_le_pow₀ h4)
  · intro lam
    set S := ∑ i, (lam i).natAbs
    have hS : (lam (Fin.last n)).natAbs ≤ S :=
      Finset.single_le_sum (f := fun i => (lam i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)
    rw [norm_mul, satakeSchur, norm_mul]
    have hd := hdet lam
    have hh := hhalf lam
    have hp := hprod (lam (Fin.last n))
    have hp' : P ^ (lam (Fin.last n)).natAbs ≤ P ^ S := pow_le_pow_right₀ hP hS
    have hM0 : 0 ≤ M := le_trans zero_le_one hM
    calc
      ‖halfModulus q lam‖ * (‖(∏ i, (x i : ℂ)) ^ lam (Fin.last n)‖ *
          ‖eval (fun i => (x i : ℂ)) (jacobiTrudi ℂ fun i => lam i - lam (Fin.last n))‖) ≤
          Q ^ ((n + 1) * S) * (P ^ S * ((n + 1).factorial *
            (2 ^ ((n + 1) + (2 * S + (n + 1))) * M ^ (2 * S + (n + 1))) ^ (n + 1))) := by
        gcongr
        exact le_trans hp hp'
      _ = (n + 1).factorial * (2 ^ ((n + 1) + (n + 1)) * M ^ (n + 1)) ^ (n + 1) *
          (Q ^ (n + 1) * P * (2 * M) ^ (2 * (n + 1))) ^ S := by
        generalize (2 : ℝ) = T
        ring_nf

end Langlands.Conductor
