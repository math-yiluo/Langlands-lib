import Langlands.Representation.Archimedean.RealInterlacedColumns

/-!
# The chain of multipliers for two interlaced induction blocks

Generic lemmas for the chain: binomial Fourier coefficients, sign matrices, the extension of a
function from `SO(4)` to `O(4)` by the determinant, steps of Frobenius maps on `SO(n)`, and the
modes at the middle block of `GL₄`.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealInterlacedJacquet

open Langlands.LocalFactor.Archimedean
open RealJacquetFrobenius RealBlockJacquet RealBlockMultiplier RealBlockRotation
  RealBlockFourierFinite RealBlockDerivative RealCharacterCrossing RealBlockFlatJacquet InductionStages

variable {n : ℕ}

/-! ## Binomial Fourier coefficients -/

section Binomial

theorem expMode_pow (k : ℤ) (l : ℕ) (t : ℝ) : expMode k t ^ l = expMode (k * l) t := by
  simp only [expMode, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem expMode_neg_arg (k : ℤ) (t : ℝ) : expMode k (-t) = expMode (-k) t := by
  simp only [expMode]
  congr 1
  push_cast
  ring

/-- `∫₀^{2π} (a e^{iσt} + b)^N e^{-iσjt} dt = 2π C(N, j) a^j b^{N-j}`. -/
theorem coeff_binom {σ : ℤ} (hσ : σ ≠ 0) (a b : ℂ) (N : ℕ) {j : ℕ} (hj : j ≤ N) :
    coeff (σ * j) (fun t => (a * expMode σ t + b) ^ N) =
      2 * (Real.pi : ℂ) * (a ^ j * b ^ (N - j) * (N.choose j : ℂ)) := by
  set c : ℕ → ℂ := fun l => a ^ l * b ^ (N - l) * (N.choose l : ℂ) with hc
  have e : (fun t => (a * expMode σ t + b) ^ N) = fun t => ∑ l ∈ Finset.range (N + 1),
      c l * expMode (σ * l) t := by
    funext t
    rw [add_pow]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow, expMode_pow, hc]
    ring
  rw [e, coeff_finset_sum_nat _ (fun l t => c l * expMode (σ * l) t)
    fun l _ => continuous_const.mul (continuous_expMode _)]
  have hterm : ∀ l : ℕ, coeff (σ * j) (fun t => c l * expMode (σ * l) t) =
      if l = j then 2 * (Real.pi : ℂ) * c l else 0 := by
    intro l
    rw [coeff_const_mul, coeff_expMode]
    by_cases hl : l = j
    · subst hl
      simp only [↓reduceIte]
      ring
    · have h' : σ * (l : ℤ) ≠ σ * j := fun h => hl (by exact_mod_cast mul_left_cancel₀ hσ h)
      simp only [h', hl, ↓reduceIte, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr (by omega))]

end Binomial

/-! ## Sign matrices of `GL₄` -/

section Signs

/-- The diagonal sign matrix `s_i` with `-1` at `i`. -/
abbrev fl (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal fun k => if k = i then -1 else 1

theorem signReflection_val4 (i : Fin 4) :
    ((signReflection 4 i : Matrix.unitaryGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = fl i :=
  rfl

theorem fl_mul_fl (i : Fin 4) : fl i * fl i = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  split_ifs <;> norm_num

theorem fl_mul_fl_mul (i : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℝ) : fl i * (fl i * X) = X := by
  rw [← Matrix.mul_assoc, fl_mul_fl, Matrix.one_mul]

theorem fl_comm (i j : Fin 4) : fl i * fl j = fl j * fl i := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  ring

theorem det_fl_mul (i : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℝ) : (fl i * X).det = -X.det := by
  rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_four]
  fin_cases i <;> simp

theorem colv_fl (u : Fin 4 → ℂ) (i j : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    colv u i (fl j * X) = (if i = j then -1 else 1) * colv u i X := by
  rw [colv_diag]
  split_ifs <;> simp

/-- **Sign equivariance from single flips.** -/
theorem isSignEq_of_flips {F : MF 4} {q : Fin 4 → ℕ}
    (h : ∀ (i : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℝ), F (fl i * X) = (-1) ^ q i * F X) :
    IsSignEq q F := by
  intro s hs X
  have hstep : ∀ (i : Fin 4) (Y : Matrix (Fin 4) (Fin 4) ℝ),
      F (Matrix.diagonal (fun k => if k = i then s i else 1) * Y) =
        ((s i : ℝ) : ℂ) ^ q i * F Y := by
    intro i Y
    rcases hs i with h1 | h1
    · rw [h1]
      simp
    · rw [h1, h i Y]
      push_cast
      ring
  have hd : Matrix.diagonal s = Matrix.diagonal (fun k => if k = 0 then s 0 else 1) *
      (Matrix.diagonal (fun k => if k = 1 then s 1 else 1) *
      (Matrix.diagonal (fun k => if k = 2 then s 2 else 1) *
       Matrix.diagonal (fun k => if k = 3 then s 3 else 1))) := by
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    fin_cases k <;> simp
  rw [hd]
  simp only [Matrix.mul_assoc]
  rw [hstep, hstep, hstep, hstep, Fin.prod_univ_four]
  ring

theorem det_eq_one_or_neg_one {κ : Matrix (Fin n) (Fin n) ℝ}
    (hκ : κ ∈ Matrix.unitaryGroup (Fin n) ℝ) : κ.det = 1 ∨ κ.det = -1 := by
  have h := (Matrix.det_of_mem_unitary hκ).1
  have h' : κ.det * κ.det = 1 := by simpa using h
  exact mul_self_eq_one_iff.mp h'

theorem fl3_rot0 (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    fl 3 * ((blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      (blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * (fl 3 * X) := by
  have h := congrArg (fun g : Langlands.GeneralLinear 4 ℝ => (g : Matrix (Fin 4) (Fin 4) ℝ))
    (signReflection_mul_blockRotation_mul_of_not_mem h40 (3 : Fin 4) ⟨by decide, by decide⟩ φ)
  simp only [Units.val_mul, Unitary.val_toUnits_apply, signReflection_val4] at h
  calc fl 3 * ((blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * X)
      = fl 3 * (blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * fl 3 * (fl 3 * X) := by
        simp only [Matrix.mul_assoc, fl_mul_fl_mul]
    _ = (blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * (fl 3 * X) := by rw [h]

theorem fl3_rot2 (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    fl 3 * ((blockRotation 4 2 φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
      (blockRotation 4 2 (-φ) : Matrix (Fin 4) (Fin 4) ℝ) * (fl 3 * X) := by
  have h := congrArg (fun g : Langlands.GeneralLinear 4 ℝ => (g : Matrix (Fin 4) (Fin 4) ℝ))
    (signReflection_mul_blockRotation_mul_of_mem h42 (3 : Fin 4) (Or.inr rfl) φ)
  simp only [Units.val_mul, Unitary.val_toUnits_apply, signReflection_val4] at h
  calc fl 3 * ((blockRotation 4 2 φ : Matrix (Fin 4) (Fin 4) ℝ) * X)
      = fl 3 * (blockRotation 4 2 φ : Matrix (Fin 4) (Fin 4) ℝ) * fl 3 * (fl 3 * X) := by
        simp only [Matrix.mul_assoc, fl_mul_fl_mul]
    _ = (blockRotation 4 2 (-φ) : Matrix (Fin 4) (Fin 4) ℝ) * (fl 3 * X) := by rw [h]

end Signs

/-! ## Extension from `SO(4)` by the determinant -/

section DetExt

/-- `F(X) = ((1 + det X)/2) G(X) + ((1 - det X)/2) G(s₃ X)`: on `O(4)` this is `G` on `SO(4)` and
`G(s₃ ·)` on the other component. -/
def detExt (G : MF 4) : MF 4 := fun X =>
  (1 + ((X.det : ℝ) : ℂ)) / 2 * G X + (1 - ((X.det : ℝ) : ℂ)) / 2 * G (fl 3 * X)

theorem detExt_of_det_one {G : MF 4} {X : Matrix (Fin 4) (Fin 4) ℝ} (h : X.det = 1) :
    detExt G X = G X := by
  simp only [detExt, h]
  norm_num

theorem detExt_of_det_neg_one {G : MF 4} {X : Matrix (Fin 4) (Fin 4) ℝ} (h : X.det = -1) :
    detExt G X = G (fl 3 * X) := by
  simp only [detExt, h]
  norm_num

theorem detExt_mem_PF {G : MF 4} (hG : G ∈ PF 4) : detExt G ∈ PF 4 := by
  have hdet := det_mem_PF (n := 4)
  have hG3 := comp_left_mem_PF (signReflection 4 3) hG
  have e : detExt G = (algebraMap ℂ (MF 4) (1 / 2) + (1 / 2 : ℂ) •
      (fun X : Matrix (Fin 4) (Fin 4) ℝ => ((X.det : ℝ) : ℂ))) * G +
      (algebraMap ℂ (MF 4) (1 / 2) - (1 / 2 : ℂ) •
        (fun X : Matrix (Fin 4) (Fin 4) ℝ => ((X.det : ℝ) : ℂ))) *
        (fun X => G ((signReflection 4 3 : Matrix (Fin 4) (Fin 4) ℝ) * X)) := by
    funext X
    simp only [detExt, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, signReflection_val4]
    ring
  rw [e]
  exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.add_mem _
    (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ hdet _)) hG)
    (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.smul_mem _ hdet _)) hG3)

/-- **Signs of the extension.** If `G(s₃ s_i X) = (-1)^{q_i} G(X)` for `i = 0, 1, 2` and `q₃` is
even, then the extension transforms under the sign matrices with the exponents `q`. -/
theorem isSignEq_detExt {G : MF 4} {q : Fin 4 → ℕ}
    (hG : ∀ i : Fin 4, i ≠ 3 → ∀ X : Matrix (Fin 4) (Fin 4) ℝ,
      G (fl 3 * (fl i * X)) = (-1) ^ q i * G X)
    (h3 : (-1 : ℂ) ^ q 3 = 1) : IsSignEq q (detExt G) := by
  refine isSignEq_of_flips fun i X => ?_
  by_cases hi : i = 3
  · subst hi
    rw [h3, one_mul]
    simp only [detExt, det_fl_mul, fl_mul_fl_mul]
    push_cast
    ring
  · have e : fl i * X = fl 3 * (fl i * (fl 3 * X)) := by
      rw [← Matrix.mul_assoc (fl i), fl_comm i 3, Matrix.mul_assoc, fl_mul_fl_mul]
    simp only [detExt, det_fl_mul]
    rw [hG i hi X]
    conv_lhs => rw [e]
    rw [hG i hi (fl 3 * X)]
    push_cast
    ring

/-- **Windows of the extension.** If `G` has the two modes `±N` along the rotations of the block
`0` or `2`, so has its extension along every orbit through `O(4)`. -/
theorem coeff_detExt_eq_zero {G A B : MF 4} {b : ℕ} (hb : b = 0 ∨ b = 2) {N : ℤ}
    (hG : ∀ (φ : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ),
      G ((blockRotation 4 b φ : Matrix (Fin 4) (Fin 4) ℝ) * X) =
        expMode N φ * A X + expMode (-N) φ * B X)
    {k : ℤ} (hk : |k| < |N|) {κ : Matrix (Fin 4) (Fin 4) ℝ}
    (hκ : κ ∈ Matrix.unitaryGroup (Fin 4) ℝ) :
    coeff k (fun φ => detExt G ((blockRotation 4 b φ : Matrix (Fin 4) (Fin 4) ℝ) * κ)) = 0 := by
  rcases det_eq_one_or_neg_one hκ with hd | hd
  · have e : (fun φ => detExt G ((blockRotation 4 b φ : Matrix (Fin 4) (Fin 4) ℝ) * κ)) =
        fun φ => expMode N φ * A κ + expMode (-N) φ * B κ := by
      funext φ
      rw [detExt_of_det_one (by rw [Matrix.det_mul, det_blockRotation, hd, one_mul]), hG]
    rw [e]
    exact coeff_two_mode_eq_zero _ _ hk
  · rcases hb with rfl | rfl
    · have e : (fun φ => detExt G ((blockRotation 4 0 φ : Matrix (Fin 4) (Fin 4) ℝ) * κ)) =
          fun φ => expMode N φ * A (fl 3 * κ) + expMode (-N) φ * B (fl 3 * κ) := by
        funext φ
        rw [detExt_of_det_neg_one (by rw [Matrix.det_mul, det_blockRotation, hd, one_mul]),
          fl3_rot0, hG]
      rw [e]
      exact coeff_two_mode_eq_zero _ _ hk
    · have e : (fun φ => detExt G ((blockRotation 4 2 φ : Matrix (Fin 4) (Fin 4) ℝ) * κ)) =
          fun φ => expMode (-N) φ * A (fl 3 * κ) + expMode (-(-N)) φ * B (fl 3 * κ) := by
        funext φ
        rw [detExt_of_det_neg_one (by rw [Matrix.det_mul, det_blockRotation, hd, one_mul]),
          fl3_rot2, hG, expMode_neg_arg, expMode_neg_arg]
      rw [e]
      exact coeff_two_mode_eq_zero _ _ (by rwa [abs_neg])

end DetExt

/-! ## Frobenius maps on `SO(n)` -/

section Frob

variable {ds' : List RealBlock}

/-- **A step of the chain on `SO(n)`.** -/
theorem frobMap_eq_on {b : ℕ} {μ : ℤ → ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
    (hJ : IsRealJacquetFunctional n (realStandardRep n ds') (realStandardLie n ds')
      (blockJacquet n ds' b μ) a e)
    {N : ℕ} {S T : Submodule ℂ (MF n)} (hS : HasExpTop b N S T) (w : KF n ds') {H : MF n}
    (hH : H ∈ S)
    (hw : ∀ κ ∈ SOset n,
      (w : Langlands.GeneralLinear n ℝ → ℂ) κ = H (κ : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ H' ∈ S, ∀ κ ∈ SOset n,
      ((frobMap hJ w : KF n _) : Langlands.GeneralLinear n ℝ → ℂ) κ =
        H' (κ : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨H', hH', h⟩ := exists_step hS hH hw μ
  refine ⟨H', hH', fun κ hκ => ?_⟩
  rw [frobMap_coe, frobFun_apply_of_mem (fun j v => (hJ.2 j v).2) w hκ.1]
  exact h κ hκ

/-- **Vanishing goes back through a step** at the modes where the multiplier is nonzero. -/
theorem blockFourierCoefficient_eq_zero_of_frobMap {b : ℕ} (hb : b + 1 < n) {μ : ℤ → ℂ}
    {a : Fin n → ℂ} {e : Fin n → Fin 2}
    (hJ : IsRealJacquetFunctional n (realStandardRep n ds') (realStandardLie n ds')
      (blockJacquet n ds' b μ) a e) (w : KF n ds')
    (h0 : ∀ κ ∈ SOset n, ((frobMap hJ w : KF n _) : Langlands.GeneralLinear n ℝ → ℂ) κ = 0)
    {j : ℤ} (hμ : μ j ≠ 0) {κ : Langlands.GeneralLinear n ℝ} (hκ : κ ∈ SOset n) :
    blockFourierCoefficient n b j w κ = 0 := by
  have h := blockFourierCoefficient_frobFun (a := a) (e := e) hb (fun j v => (hJ.2 j v).2) w
    hκ.1 j
  have h1 : blockFourierCoefficient n b j
      ((frobMap hJ w : KF n _) : Langlands.GeneralLinear n ℝ → ℂ) κ = 0 := by
    rw [blockFourierCoefficient_eq_coeff]
    have e : (fun θ => ((frobMap hJ w : KF n _) : Langlands.GeneralLinear n ℝ → ℂ)
        (blockRotation n b θ * κ)) = 0 :=
      funext fun θ => h0 _ (rot_mul_mem_SOset hκ b θ)
    rw [e, coeff_zero_fun]
  rw [frobMap_coe] at h1
  rw [h1] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hμ

/-- A function of the standard module vanishing on `SO(n)` has vanishing block Fourier
coefficients there. -/
theorem blockFourierCoefficient_eq_zero_of_eq_on {b : ℕ} {f : Langlands.GeneralLinear n ℝ → ℂ}
    (h0 : ∀ κ ∈ SOset n, f κ = 0) (j : ℤ) {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ SOset n) : blockFourierCoefficient n b j f κ = 0 := by
  rw [blockFourierCoefficient_eq_coeff]
  have e : (fun θ => f (blockRotation n b θ * κ)) = 0 :=
    funext fun θ => h0 _ (rot_mul_mem_SOset hκ b θ)
  rw [e, coeff_zero_fun]

end Frob

/-! ## Modes at the middle block of `GL₄` -/

section Middle

theorem sign_mem_SOset {κ : Langlands.GeneralLinear 4 ℝ} (hκ : κ ∈ SOset 4) :
    (Unitary.toUnits (signReflection 4 3) * (Unitary.toUnits (signReflection 4 2) * κ) :
      Langlands.GeneralLinear 4 ℝ) ∈ SOset 4 := by
  refine ⟨(unitaryCompact ℝ 4).mul_mem ?_ ((unitaryCompact ℝ 4).mul_mem ?_ hκ.1), ?_⟩
  · exact (signReflection 4 3).2
  · exact (signReflection 4 2).2
  · rw [Units.val_mul, Units.val_mul, Unitary.val_toUnits_apply, Unitary.val_toUnits_apply,
      signReflection_val4, signReflection_val4, det_fl_mul, det_fl_mul, hκ.2]
    ring

theorem sign_val (κ : Langlands.GeneralLinear 4 ℝ) :
    ((Unitary.toUnits (signReflection 4 3) * (Unitary.toUnits (signReflection 4 2) * κ) :
      Langlands.GeneralLinear 4 ℝ) : Matrix (Fin 4) (Fin 4) ℝ) =
      fl 3 * (fl 2 * (κ : Matrix (Fin 4) (Fin 4) ℝ)) := by
  rw [Units.val_mul, Units.val_mul, Unitary.val_toUnits_apply, Unitary.val_toUnits_apply,
    signReflection_val4, signReflection_val4]

/-- `Φ_{-j}(w)(g) = (-1)^{e₂ + e₃} Φ_j(w)(s₃ s₂ g)` at the block `1`. -/
theorem blockFourierCoefficient_neg_one {τ : Fin 4 → ℂ} {e : Fin 4 → Fin 2}
    (w : KF 4 (PL τ e)) (j : ℤ) (g : Langlands.GeneralLinear 4 ℝ) :
    blockFourierCoefficient 4 1 (-j) w g =
      (-1) ^ ((e 2).val + (e 3).val) * blockFourierCoefficient 4 1 j w
        (Unitary.toUnits (signReflection 4 3) * (Unitary.toUnits (signReflection 4 2) * g)) := by
  have hχ : ∀ i : ℕ, realPositionCharacter (PL τ e) i 1 = 1 :=
    RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _
  have h1 := blockFourierCoefficient_signReflection_mul_of_not_mem h41 hχ w.2.1.1 3
    ⟨by decide, by decide⟩ j (Unitary.toUnits (signReflection 4 2) * g)
  have h2 := blockFourierCoefficient_signReflection_mul_of_mem h41 hχ w.2.1.1 2
    (Or.inr rfl) j g
  rw [h1, h2, PL_position_neg_one, PL_position_neg_one, pow_add]
  have hsq2 := neg_one_pow_mul_self (e 2).val
  have hsq3 := neg_one_pow_mul_self (e 3).val
  linear_combination (-(blockFourierCoefficient 4 1 (-j) (w : Langlands.GeneralLinear 4 ℝ → ℂ) g) *
    ((-1 : ℂ) ^ (e 3).val) ^ 2) * hsq2 +
    (-(blockFourierCoefficient 4 1 (-j) (w : Langlands.GeneralLinear 4 ℝ → ℂ) g)) * hsq3

/-- **Only the modes `±N` at the middle block.** If the window `|j| + 1 < N` vanishes on `O(4)`,
the parity class of the block is that of `N`, and `w` agrees on `SO(4)` with a function having an
expansion of order `N` along the block, then all other modes of `w` vanish on `SO(4)`. -/
theorem blockFourierCoefficient_one_eq_zero {τ : Fin 4 → ℂ} {e : Fin 4 → Fin 2}
    (w : KF 4 (PL τ e)) {N : ℕ} {H : MF 4} {P : Polynomial (MF 4)} (hP : IsExpansion 1 N H P)
    (hwH : ∀ κ ∈ SOset 4,
      (w : Langlands.GeneralLinear 4 ℝ → ℂ) κ = H (κ : Matrix (Fin 4) (Fin 4) ℝ))
    (hwin : ∀ j : ℤ, |j| + 1 < N → ∀ κ ∈ unitaryCompact ℝ 4,
      blockFourierCoefficient 4 1 j w κ = 0)
    (hpar : Even ((N : ℤ) - ((par h41 e : ℕ) : ℤ))) {j : ℤ} (hj : j ≠ N) (hj' : j ≠ -N)
    {κ : Langlands.GeneralLinear 4 ℝ} (hκ : κ ∈ SOset 4) :
    blockFourierCoefficient 4 1 j w κ = 0 := by
  by_cases h1 : |j| + 1 < N
  · exact hwin j h1 κ hκ.1
  by_cases h2 : (N : ℤ) < |j|
  · rw [blockFourierCoefficient_eq_of_expansion hP hwH hκ j, ite_eq_right]
    rintro ⟨ha, hb⟩
    rcases abs_cases j with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  · have h3 : |j| + 1 = N := by
      have : |j| ≠ N := fun h => by
        rcases abs_eq (by omega : (0 : ℤ) ≤ N) |>.mp h with h | h
        · exact hj h
        · exact hj' h
      omega
    refine blockFourierCoefficient_eq_zero_of_not_even h41 (PL_parity h41 τ e) w ?_ κ
    intro hev
    rw [Int.even_iff] at hev hpar
    rcases abs_cases j with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega

end Middle

end RealInterlacedJacquet

end Langlands.Archimedean
