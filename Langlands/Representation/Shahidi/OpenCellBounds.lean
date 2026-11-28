import Langlands.Representation.Shahidi.OpenCellValue
import Langlands.Representation.Conductor.SphericalDualParameters
import Mathlib.Data.Sym.Card

/-! # Elementary bounds for Schur functions and half moduli -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.GeneralLinear.Spherical MvPolynomial

/-- The determinant of a matrix with entries of norm at most `x`. -/
theorem norm_det_le_of_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) {x : ℝ}
    (hx : ∀ i j, ‖A i j‖ ≤ x) : ‖A.det‖ ≤ (m.factorial : ℝ) * x ^ m := by
  have hx0 : ∀ i j, 0 ≤ x := fun i j => (norm_nonneg _).trans (hx i j)
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin m), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), x ^ m := by
        apply Finset.sum_le_sum
        intro σ _
        have hprod : ‖∏ i, A (σ i) i‖ ≤ x ^ m := by
          rw [norm_prod]
          calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : Fin m, x :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
            _ = x ^ m := by simp
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · rw [h, one_smul]
          exact hprod
        · rw [h, Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul, norm_neg]
          exact hprod
    _ = (m.factorial : ℝ) * x ^ m := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm]

theorem norm_multiset_map_prod_le {ι : Type*} (x : ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hx : ∀ i, ‖x i‖ ≤ M) (s : Multiset ι) :
    ‖(s.map x).prod‖ ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (hx a) ih (norm_nonneg _) hM

/-- `|h_k(x)| ≤ 2^(m+k) M^k` when every `|x_i| ≤ M`. -/
theorem norm_eval_hsymm_le {m : ℕ} (x : Fin m → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hx : ∀ i, ‖x i‖ ≤ M) (k : ℕ) :
    ‖eval x (hsymm (Fin m) ℂ k)‖ ≤ 2 ^ (m + k) * M ^ k := by
  rw [hsymm, map_sum]
  calc ‖∑ s : Sym (Fin m) k, eval x (s.1.map X).prod‖
      ≤ ∑ s : Sym (Fin m) k, ‖eval x (s.1.map X).prod‖ := norm_sum_le _ _
    _ ≤ ∑ _s : Sym (Fin m) k, M ^ k := by
        apply Finset.sum_le_sum
        intro s _
        rw [map_multiset_prod, Multiset.map_map]
        have h := norm_multiset_map_prod_le x hM hx s.1
        rw [s.2] at h
        simpa [Function.comp_def] using h
    _ = (Fintype.card (Sym (Fin m) k) : ℝ) * M ^ k := by
        simp [Finset.sum_const, Finset.card_univ]
    _ ≤ 2 ^ (m + k) * M ^ k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM k)
        rw [Sym.card_sym_fin_eq_multichoose, Nat.multichoose_eq]
        have h1 := Nat.choose_le_two_pow (m + k - 1) k
        have h2 : 2 ^ (m + k - 1) ≤ 2 ^ (m + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast h1.trans h2

/-- `|h_k(x)| ≤ 2^(m+K) M^K` for `k ≤ K` (with `h_k = 0` for `k < 0`), when `|x_i| ≤ M`
and `1 ≤ M`. -/
theorem norm_eval_completeSymm_le {m : ℕ} (x : Fin m → ℂ) {M : ℝ} (hM : 1 ≤ M)
    (hx : ∀ i, ‖x i‖ ≤ M) {k : ℤ} {K : ℕ} (hk : k ≤ K) :
    ‖eval x (completeSymm (Fin m) ℂ k)‖ ≤ 2 ^ (m + K) * M ^ K := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hpos : 0 ≤ (2 : ℝ) ^ (m + K) * M ^ K := by positivity
  unfold completeSymm
  split_ifs with h0
  · refine (norm_eval_hsymm_le x hM0 hx k.toNat).trans ?_
    have hkK : k.toNat ≤ K := by omega
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) (pow_le_pow_right₀ hM hkK)
      (pow_nonneg hM0 _) (by positivity)
  · simpa using hpos

/-- A bound for the Schur function of a nonnegative antitone weight with total `D`. -/
theorem norm_satakeSchur_le {n : ℕ} (x : Fin (n + 1) → ℂˣ) {M : ℝ} (hM : 1 ≤ M)
    (hx : ∀ i, ‖(x i : ℂ)‖ ≤ M) {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam)
    (hlast : 0 ≤ lam (Fin.last n)) {D : ℕ} (hD : ∑ i, lam i = D) :
    ‖satakeSchur x lam‖ ≤ ((n + 1).factorial : ℝ) * (2 ^ (2 * (n + 1)) * M ^ (n + 1)) ^ (n + 1) *
      (2 ^ (n + 1) * M ^ (2 * (n + 1))) ^ D := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hnonneg : ∀ i, 0 ≤ lam i := fun i => hlast.trans (hlam (Fin.le_last i))
  have hle : ∀ i, lam i ≤ D := by
    intro i
    rw [← hD]
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  set α : Fin (n + 1) → ℤ := fun i => lam i - lam (Fin.last n) with hα
  -- the determinant
  have hdet : ‖eval (fun i => (x i : ℂ)) (jacobiTrudi ℂ α)‖ ≤
      ((n + 1).factorial : ℝ) * (2 ^ ((n + 1) + (D + n)) * M ^ (D + n)) ^ (n + 1) := by
    rw [jacobiTrudi, RingHom.map_det]
    apply norm_det_le_of_le
    intro i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    apply norm_eval_completeSymm_le _ hM hx
    have h1 := hle i
    have h2 := hnonneg (Fin.last n)
    have h3 : (j : ℤ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp j.isLt
    have h4 : (0 : ℤ) ≤ i := by positivity
    have hαi : α i = lam i - lam (Fin.last n) := rfl
    push_cast
    omega
  -- the determinant power
  have hprod : ‖(∏ i, (x i : ℂ)) ^ lam (Fin.last n)‖ ≤ M ^ ((n + 1) * D) := by
    have hlastD := hle (Fin.last n)
    obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hlast
    rw [he, zpow_natCast, norm_pow, norm_prod]
    have hP : ∏ i, ‖(x i : ℂ)‖ ≤ M ^ (n + 1) := by
      calc ∏ i, ‖(x i : ℂ)‖ ≤ ∏ _i : Fin (n + 1), M :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hx i)
        _ = M ^ (n + 1) := by simp
    have heD : e ≤ D := by omega
    calc (∏ i, ‖(x i : ℂ)‖) ^ e ≤ (M ^ (n + 1)) ^ e :=
          pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => norm_nonneg _) hP e
      _ ≤ (M ^ (n + 1)) ^ D := pow_le_pow_right₀ (one_le_pow₀ hM) heD
      _ = M ^ ((n + 1) * D) := by rw [← pow_mul]
  rw [satakeSchur, norm_mul]
  calc ‖(∏ i, (x i : ℂ)) ^ lam (Fin.last n)‖ *
        ‖eval (fun i => (x i : ℂ)) (jacobiTrudi ℂ fun i => lam i - lam (Fin.last n))‖
      ≤ M ^ ((n + 1) * D) * (((n + 1).factorial : ℝ) *
          (2 ^ ((n + 1) + (D + n)) * M ^ (D + n)) ^ (n + 1)) :=
        mul_le_mul hprod hdet (norm_nonneg _) (by positivity)
    _ ≤ ((n + 1).factorial : ℝ) * (2 ^ (2 * (n + 1)) * M ^ (n + 1)) ^ (n + 1) *
          (2 ^ (n + 1) * M ^ (2 * (n + 1))) ^ D := by
        have e1 : (2 : ℝ) ^ ((n + 1) + (D + n)) * M ^ (D + n) ≤
            (2 ^ (2 * (n + 1)) * M ^ (n + 1)) * (2 ^ D * M ^ D) := by
          rw [show (2 * (n + 1)) = (n + 1) + (n + 1) by ring]
          have : (2 : ℝ) ^ ((n + 1) + (D + n)) ≤ 2 ^ ((n + 1) + (n + 1)) * 2 ^ D := by
            rw [← pow_add]
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          have : M ^ (D + n) ≤ M ^ (n + 1) * M ^ D := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hM (by omega)
          nlinarith [pow_nonneg hM0 (D + n), pow_nonneg hM0 D, pow_nonneg hM0 (n + 1),
            pow_pos (show (0 : ℝ) < 2 by norm_num) ((n + 1) + (D + n)),
            pow_pos (show (0 : ℝ) < 2 by norm_num) D,
            pow_pos (show (0 : ℝ) < 2 by norm_num) ((n + 1) + (n + 1))]
        calc M ^ ((n + 1) * D) * (((n + 1).factorial : ℝ) *
              (2 ^ ((n + 1) + (D + n)) * M ^ (D + n)) ^ (n + 1))
            ≤ M ^ ((n + 1) * D) * (((n + 1).factorial : ℝ) *
              ((2 ^ (2 * (n + 1)) * M ^ (n + 1)) * (2 ^ D * M ^ D)) ^ (n + 1)) := by
                gcongr
          _ = ((n + 1).factorial : ℝ) * (2 ^ (2 * (n + 1)) * M ^ (n + 1)) ^ (n + 1) *
              (2 ^ (n + 1) * M ^ (2 * (n + 1))) ^ D := by
                ring

/-- `|δ_B^(1/2)(ϖ^λ)| ≤ q^(n D)` when `∑ |λ_i| ≤ D`. -/
theorem norm_halfModulus_le {q : ℕ} (hq : 1 ≤ q) {n : ℕ} (lam : Fin (n + 1) → ℤ) {D : ℕ}
    (hD : ∑ i, |lam i| ≤ D) : ‖halfModulus q lam‖ ≤ (q : ℝ) ^ (n * D) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs1 : (1 : ℝ) ≤ Real.sqrt q := by
    rw [Real.one_le_sqrt]
    exact hq1
  have hsq : Real.sqrt q ≤ q := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  set S := ∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i with hS
  have hSle : -S ≤ (n * D : ℕ) := by
    have h1 : -S ≤ ∑ i : Fin (n + 1), (n : ℤ) * |lam i| := by
      rw [hS, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i _
      have hi : (i : ℤ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
      have hi0 : (0 : ℤ) ≤ i := by positivity
      have habs : |((n : ℤ) - 2 * (i : ℤ))| ≤ n := by
        rw [abs_le]
        constructor <;> omega
      calc -(((n : ℤ) - 2 * (i : ℤ)) * lam i) ≤ |((n : ℤ) - 2 * (i : ℤ)) * lam i| :=
            neg_le_abs _
        _ = |((n : ℤ) - 2 * (i : ℤ))| * |lam i| := abs_mul _ _
        _ ≤ (n : ℤ) * |lam i| := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    rw [← Finset.mul_sum] at h1
    push_cast
    nlinarith [abs_nonneg (lam 0)]
  rw [halfModulus, norm_zpow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt q ^ (-S) ≤ Real.sqrt q ^ ((n * D : ℕ) : ℤ) :=
        zpow_le_zpow_right₀ hs1 hSle
    _ = Real.sqrt q ^ (n * D) := zpow_natCast _ _
    _ ≤ (q : ℝ) ^ (n * D) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq _

section Whittaker

open Langlands.GeneralLinear.Iwasawa Langlands.Conductor

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation F Γ₀} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ) {n : ℕ}
  {θ : upperUnipotent (n + 1) F →* ℂˣ}

/-- The spherical Whittaker function at `u ϖ^λ` for antitone `λ`. -/
theorem sphericalWhittaker_unipotent_mul_torus (hθ : IsIntegrallyTrivial v θ) (q : ℕ)
    (x : Fin (n + 1) → ℂˣ) {u : Langlands.GeneralLinear (n + 1) F}
    (hu : u ∈ upperUnipotent (n + 1) F) {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) :
    sphericalWhittaker hϖ θ q x (u * torus ϖ lam) =
      (θ ⟨u, hu⟩ : ℂ) * (halfModulus q lam * satakeSchur x lam) := by
  have h := cellFunction_of_antitone hϖ (fun lam => halfModulus q lam * satakeSchur x lam) hθ
    ⟨u, hu⟩ hlam (one_mem (integralSubgroup v.integer n))
  rw [mul_one] at h
  exact h

/-- Off the antitone exponents the spherical Whittaker function vanishes at `u ϖ^λ`. -/
theorem sphericalWhittaker_unipotent_mul_torus_of_not_antitone (q : ℕ)
    (x : Fin (n + 1) → ℂˣ) {u : Langlands.GeneralLinear (n + 1) F}
    (hu : u ∈ upperUnipotent (n + 1) F) {lam : Fin (n + 1) → ℤ} (hlam : ¬ Antitone lam) :
    sphericalWhittaker hϖ θ q x (u * torus ϖ lam) = 0 := by
  apply cellFunction_of_not_antitone
  rwa [exponent_eq hϖ hu (one_mem (integralSubgroup v.integer n)) (mul_one _).symm]

/-- A bound for the spherical Whittaker function at `u ϖ^λ` with `λ ≥ 0` of total `D`. -/
theorem norm_sphericalWhittaker_le_of_nonneg (hθ : IsIntegrallyTrivial v θ)
    (hθ1 : ∀ w, ‖(θ w : ℂ)‖ = 1) {q : ℕ} (hq : 1 ≤ q) (x : Fin (n + 1) → ℂˣ) {M : ℝ}
    (hM : 1 ≤ M) (hx : ∀ i, ‖(x i : ℂ)‖ ≤ M) {u : Langlands.GeneralLinear (n + 1) F}
    (hu : u ∈ upperUnipotent (n + 1) F) {lam : Fin (n + 1) → ℤ} (hnn : ∀ i, 0 ≤ lam i)
    {D : ℕ} (hD : ∑ i, lam i = D) :
    ‖sphericalWhittaker hϖ θ q x (u * torus ϖ lam)‖ ≤
      (q : ℝ) ^ (n * D) * (((n + 1).factorial : ℝ) * (2 ^ (2 * (n + 1)) * M ^ (n + 1)) ^ (n + 1) *
        (2 ^ (n + 1) * M ^ (2 * (n + 1))) ^ D) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  by_cases hlam : Antitone lam
  · rw [sphericalWhittaker_unipotent_mul_torus hϖ hθ q x hu hlam, norm_mul, hθ1, one_mul,
      norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
    · apply norm_halfModulus_le hq
      calc ∑ i, |lam i| = ∑ i, lam i := Finset.sum_congr rfl fun i _ => abs_of_nonneg (hnn i)
        _ ≤ D := hD.le
    · exact norm_satakeSchur_le x hM hx hlam (hnn _) hD
  · rw [sphericalWhittaker_unipotent_mul_torus_of_not_antitone hϖ q x hu hlam, norm_zero]
    positivity

/-- A bound for the spherical Whittaker function at `u ϖ^μ` with `μ ≤ 0` of total `-D`, in
terms of a bound for the inverse parameters. -/
theorem norm_sphericalWhittaker_le_of_nonpos (hθ : IsIntegrallyTrivial v θ)
    (hθ1 : ∀ w, ‖(θ w : ℂ)‖ = 1) {q : ℕ} (hq : 1 ≤ q) (x : Fin (n + 1) → ℂˣ) {M : ℝ}
    (hM : 1 ≤ M) (hx : ∀ i, ‖((x i)⁻¹ : ℂ)‖ ≤ M) {u : Langlands.GeneralLinear (n + 1) F}
    (hu : u ∈ upperUnipotent (n + 1) F) {lam : Fin (n + 1) → ℤ} (hnp : ∀ i, lam i ≤ 0)
    {D : ℕ} (hD : ∑ i, lam i = -D) :
    ‖sphericalWhittaker hϖ θ q x (u * torus ϖ lam)‖ ≤
      (q : ℝ) ^ (n * D) * (((n + 1).factorial : ℝ) * (2 ^ (2 * (n + 1)) * M ^ (n + 1)) ^ (n + 1) *
        (2 ^ (n + 1) * M ^ (2 * (n + 1))) ^ D) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  by_cases hlam : Antitone lam
  · rw [sphericalWhittaker_unipotent_mul_torus hϖ hθ q x hu hlam, norm_mul, hθ1, one_mul,
      norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
    · apply norm_halfModulus_le hq
      calc ∑ i, |lam i| = ∑ i, -lam i := Finset.sum_congr rfl fun i _ => abs_of_nonpos (hnp i)
        _ = D := by rw [Finset.sum_neg_distrib, hD, neg_neg]
        _ ≤ D := le_rfl
    · have hinv := Conductor.satakeSchur_inv (x⁻¹) hlam
      rw [inv_inv] at hinv
      rw [hinv]
      apply norm_satakeSchur_le x⁻¹ hM (fun i => by simpa using hx i)
        ((Conductor.antitone_dualWeight_iff lam).2 hlam)
      · simp only [Conductor.dualWeight, Fin.rev_last]
        exact neg_nonneg.2 (hnp 0)
      · simp only [Conductor.dualWeight]
        rw [Finset.sum_neg_distrib]
        have hrev : ∑ i, lam (Fin.rev i) = ∑ i, lam i :=
          Equiv.sum_comp Fin.revPerm (fun i => lam i)
        rw [hrev, hD, neg_neg]
  · rw [sphericalWhittaker_unipotent_mul_torus_of_not_antitone hϖ q x hu hlam, norm_zero]
    positivity

end Whittaker

end Langlands.Shahidi.OpenCell
