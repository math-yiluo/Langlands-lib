import Langlands.Representation.Archimedean.RealBlockLeftDerivative
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Mathlib.Analysis.ODE.Gronwall

/-!
# Propagating vanishing block Fourier coefficients from `O(N)` to `GL_N(ℝ)`

Let `φ` be a smooth function on `GL_N(ℝ)` with `φ(exp(diag x) u g) = exp(∑ αᵢ xᵢ) φ(g)` for
upper unipotent `u`, and suppose `α_p - α_{p+1} = m + 1` for a natural number `m`. If the block
Fourier coefficients `Φ_j(φ)` in the coordinates `p, p + 1` vanish on `O(N)` for all `j` in the
window `|j| < m`, `j ≡ m + 1 (mod 2)`, then they vanish on all of `GL_N(ℝ)`
(`blockFourierCoefficient_window_eq_zero`).

Along the paths `t ↦ (1 + t (u - 1)) g` and `t ↦ exp(t L) g` (`L` diagonal) the coefficients
of the window satisfy a linear system of differential equations (the tridiagonal formula of
`RealBlockLeftDerivative`), which is closed because the coefficients linking the window to its
outside vanish when `α_p - α_{p+1} = m + 1`. Grönwall's inequality then propagates the vanishing
from `O(N)` along the Iwasawa decomposition `g = exp(diag l) u k`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealBlockPropagation

open RealBlockRotation RealPrincipalSeriesDuality RealBlockDerivative

/-! ## The window -/

/-- The window `{j : |j| < m, j ≡ m + 1 (mod 2)}` of Fourier indices. -/
def window (m : ℕ) : Finset ℤ :=
  (Finset.Ioo (-(m : ℤ)) m).filter fun j => Even (j + m + 1)

theorem mem_window {m : ℕ} {j : ℤ} : j ∈ window m ↔ |j| < m ∧ Even (j + m + 1) := by
  rw [window, Finset.mem_filter, Finset.mem_Ioo, abs_lt]

/-- The only index of the window whose predecessor `j - 2` leaves it is `j = 1 - m`. -/
theorem eq_of_mem_window_of_sub_two_not_mem {m : ℕ} {j : ℤ} (hj : j ∈ window m)
    (hj2 : j - 2 ∉ window m) : j = 1 - m := by
  rw [mem_window, abs_lt] at hj
  obtain ⟨⟨h1, h2⟩, ⟨k, hk⟩⟩ := hj
  have h3 : ¬ (-(m : ℤ) < j - 2 ∧ j - 2 < m) := fun hh =>
    hj2 (mem_window.mpr ⟨abs_lt.mpr hh, ⟨k - 1, by omega⟩⟩)
  omega

/-- The only index of the window whose successor `j + 2` leaves it is `j = m - 1`. -/
theorem eq_of_mem_window_of_add_two_not_mem {m : ℕ} {j : ℤ} (hj : j ∈ window m)
    (hj2 : j + 2 ∉ window m) : j = m - 1 := by
  rw [mem_window, abs_lt] at hj
  obtain ⟨⟨h1, h2⟩, ⟨k, hk⟩⟩ := hj
  have h3 : ¬ (-(m : ℤ) < j + 2 ∧ j + 2 < m) := fun hh =>
    hj2 (mem_window.mpr ⟨abs_lt.mpr hh, ⟨k + 1, by omega⟩⟩)
  omega

/-! ## A closed linear system on the window -/

/-- Functions `F j`, `j` in the window, with `F j' = a_j F_j + b_j (m + 1 + j - 2) F_{j-2} +
c_j (m + 1 - j - 2) F_{j+2}` and `F j 0 = 0` vanish for `t ≥ 0`: the system is closed on the
window, because the coefficient of `F_{j-2}` (resp. `F_{j+2}`) vanishes when `j - 2` (resp.
`j + 2`) leaves it. Proof by Grönwall's inequality. -/
theorem window_ode {m : ℕ} {F : ℤ → ℝ → ℂ} (a b c : ℤ → ℂ)
    (hF : ∀ j ∈ window m, ∀ t : ℝ, HasDerivAt (F j)
      (a j * F j t + b j * ((m : ℂ) + 1 + j - 2) * F (j - 2) t +
        c j * ((m : ℂ) + 1 - j - 2) * F (j + 2) t) t)
    (h0 : ∀ j ∈ window m, F j 0 = 0) {t : ℝ} (ht : 0 ≤ t) : ∀ j ∈ window m, F j t = 0 := by
  set W := window m with hW
  let y : ℝ → (W → ℂ) := fun s i => F i s
  let y' : ℝ → (W → ℂ) := fun s i =>
    a i * F i s + b i * ((m : ℂ) + 1 + ((i : ℤ) : ℂ) - 2) * F ((i : ℤ) - 2) s +
      c i * ((m : ℂ) + 1 - ((i : ℤ) : ℂ) - 2) * F ((i : ℤ) + 2) s
  have hy : ∀ s, HasDerivAt y (y' s) s := fun s => hasDerivAt_pi.mpr fun i => hF i i.2 s
  set K : ℝ := ∑ j ∈ W, (‖a j‖ + ‖b j * ((m : ℂ) + 1 + j - 2)‖ + ‖c j * ((m : ℂ) + 1 - j - 2)‖)
    with hK
  have hle : ∀ (s : ℝ) (i : ℤ), i ∈ W → ‖F i s‖ ≤ ‖y s‖ := fun s i hi =>
    norm_le_pi_norm (y s) ⟨i, hi⟩
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun j _ => by positivity
  have hbd : ∀ s, ‖y' s‖ ≤ K * ‖y s‖ := by
    intro s
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have hi := i.2
    have t1 : ‖a i * F i s‖ ≤ ‖a i‖ * ‖y s‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hle s i hi) (norm_nonneg _)
    have t2 : ‖b i * ((m : ℂ) + 1 + ((i : ℤ) : ℂ) - 2) * F ((i : ℤ) - 2) s‖ ≤
        ‖b i * ((m : ℂ) + 1 + ((i : ℤ) : ℂ) - 2)‖ * ‖y s‖ := by
      by_cases h2 : (i : ℤ) - 2 ∈ W
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hle s _ h2) (norm_nonneg _)
      · have e := eq_of_mem_window_of_sub_two_not_mem hi h2
        have e' : ((m : ℂ) + 1 + ((i : ℤ) : ℂ) - 2) = 0 := by
          rw [e]
          push_cast
          ring
        rw [e']
        simp
    have t3 : ‖c i * ((m : ℂ) + 1 - ((i : ℤ) : ℂ) - 2) * F ((i : ℤ) + 2) s‖ ≤
        ‖c i * ((m : ℂ) + 1 - ((i : ℤ) : ℂ) - 2)‖ * ‖y s‖ := by
      by_cases h2 : (i : ℤ) + 2 ∈ W
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hle s _ h2) (norm_nonneg _)
      · have e := eq_of_mem_window_of_add_two_not_mem hi h2
        have e' : ((m : ℂ) + 1 - ((i : ℤ) : ℂ) - 2) = 0 := by
          rw [e]
          push_cast
          ring
        rw [e']
        simp
    have hsum : ‖a i‖ + ‖b i * ((m : ℂ) + 1 + ((i : ℤ) : ℂ) - 2)‖ +
        ‖c i * ((m : ℂ) + 1 - ((i : ℤ) : ℂ) - 2)‖ ≤ K :=
      Finset.single_le_sum (f := fun j : ℤ => ‖a j‖ + ‖b j * ((m : ℂ) + 1 + j - 2)‖ +
        ‖c j * ((m : ℂ) + 1 - j - 2)‖) (fun j _ => by positivity) hi
    calc ‖y' s i‖ ≤ ‖a i * F i s‖ + ‖b i * ((m : ℂ) + 1 + ((i : ℤ) : ℂ) - 2) * F ((i : ℤ) - 2) s‖ +
          ‖c i * ((m : ℂ) + 1 - ((i : ℤ) : ℂ) - 2) * F ((i : ℤ) + 2) s‖ := norm_add₃_le
      _ ≤ (‖a i‖ + ‖b i * ((m : ℂ) + 1 + ((i : ℤ) : ℂ) - 2)‖ +
          ‖c i * ((m : ℂ) + 1 - ((i : ℤ) : ℂ) - 2)‖) * ‖y s‖ := by
        rw [add_mul, add_mul]
        linarith
      _ ≤ K * ‖y s‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := y) (f' := y') (K := K)
    (a := 0) (b := t) (fun s _ => (hy s).continuousAt.continuousWithinAt)
    (fun s _ => (hy s).hasDerivWithinAt) (funext fun i => h0 i i.2) (fun s _ => hbd s) t
    ⟨ht, le_rfl⟩
  intro j hj
  exact congrFun hz ⟨j, hj⟩

/-! ## Two paths in the Borel subgroup -/

variable {N p : ℕ} {φ : Langlands.GeneralLinear N ℝ → ℂ}

/-- Vanishing on the window propagates from `g` to `u g` for `u` upper unipotent, along the
path `t ↦ (1 + t (u - 1)) g`, whose velocity is `A(t) γ(t)` with `A(t) = (u - 1)(1 + t(u - 1))⁻¹`
upper triangular with zero diagonal and `A(t)_{p,p+1} = u_{p,p+1}`. -/
theorem window_eq_zero_upperUnipotent_mul (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    {m : ℕ} (hδ : α (ia h) - α (ib h) = m + 1) (u : upperUnipotent N ℝ)
    (g : Langlands.GeneralLinear N ℝ)
    (h0 : ∀ j ∈ window m, blockFourierCoefficient N p j φ g = 0) :
    ∀ j ∈ window m,
      blockFourierCoefficient N p j φ ((u : Langlands.GeneralLinear N ℝ) * g) = 0 := by
  set Nm : Matrix (Fin N) (Fin N) ℝ :=
    ((u : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) - 1 with hNm
  have hNu : Nm.IsUpperTriangular := u.2.1.sub Matrix.blockTriangular_one
  have hNd : ∀ i, Nm i i = 0 := fun i => by
    simp only [hNm, Matrix.sub_apply, Matrix.one_apply_eq]
    rw [show ((u : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i i = 1 from u.2.2 i,
      sub_self]
  set γ : ℝ → Langlands.GeneralLinear N ℝ := fun t =>
    ((unipotentLine Nm hNu hNd t : upperUnipotent N ℝ) : Langlands.GeneralLinear N ℝ) * g
    with hγ
  have hγv : ∀ t, (γ t : Matrix (Fin N) (Fin N) ℝ) =
      (1 + t • Nm) * (g : Matrix (Fin N) (Fin N) ℝ) := fun t => by
    rw [hγ, Units.val_mul, unipotentLine_val]
  have hγ0 : γ 0 = g := by
    apply Units.ext
    rw [hγv, zero_smul, add_zero, one_mul]
  have hγ1 : γ 1 = (u : Langlands.GeneralLinear N ℝ) * g := by
    apply Units.ext
    rw [hγv, one_smul, hNm, add_sub_cancel, Units.val_mul]
  have hγc : ContDiff ℝ 1 fun t => (γ t : Matrix (Fin N) (Fin N) ℝ) := by
    have e : (fun t => (γ t : Matrix (Fin N) (Fin N) ℝ)) =
        fun t : ℝ => (1 + t • Nm) * (g : Matrix (Fin N) (Fin N) ℝ) := funext hγv
    rw [e]
    exact (contDiff_const.add (contDiff_id.smul contDiff_const)).mul contDiff_const
  set v : ℝ := Nm (ia h) (ib h) with hv
  let F : ℤ → ℝ → ℂ := fun j t => blockFourierCoefficient N p j φ (γ t)
  have hF : ∀ j ∈ window m, ∀ t : ℝ, HasDerivAt (F j)
      ((-(Complex.I * (v : ℂ) * j / 2)) * F j t +
        (Complex.I * (v : ℂ) / 4) * ((m : ℂ) + 1 + j - 2) * F (j - 2) t +
        (-(Complex.I * (v : ℂ)) / 4) * ((m : ℂ) + 1 - j - 2) * F (j + 2) t) t := by
    intro j _ t
    set w : upperUnipotent N ℝ := (unipotentLine Nm hNu hNd t)⁻¹ with hw
    set A : Matrix (Fin N) (Fin N) ℝ :=
      Nm * ((w : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) with hA
    have hAu : A.IsUpperTriangular := hNu.mul w.2.1
    have hwl : ((w : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) * (1 + t • Nm) = 1 := by
      rw [← unipotentLine_val Nm hNu hNd t, hw, Subgroup.coe_inv, Units.inv_mul]
    have hγ' : HasDerivAt (fun s => (γ s : Matrix (Fin N) (Fin N) ℝ))
        (A * (γ t : Matrix (Fin N) (Fin N) ℝ)) t := by
      have e : (fun t => (γ t : Matrix (Fin N) (Fin N) ℝ)) =
          fun t : ℝ => (1 + t • Nm) * (g : Matrix (Fin N) (Fin N) ℝ) := funext hγv
      rw [e]
      have hd : HasDerivAt (fun t : ℝ => (1 + t • Nm) * (g : Matrix (Fin N) (Fin N) ℝ))
          (Nm * (g : Matrix (Fin N) (Fin N) ℝ)) t := by
        simpa using (((hasDerivAt_id t).smul_const Nm).const_add 1).mul_const
          (g : Matrix (Fin N) (Fin N) ℝ)
      refine hd.congr_deriv ?_
      rw [hγv, hA, mul_assoc, ← mul_assoc _ (1 + t • Nm), hwl, one_mul]
    have hAd : ∀ i, A i i = 0 := fun i => by
      rw [hA, RealJacquetFrobenius.upper_mul_apply_self hNu w.2.1 i, hNd, zero_mul]
    have hApq : A (ia h) (ib h) = v := by
      rw [hA, Matrix.mul_apply, Finset.sum_eq_single (ib h)]
      · rw [show ((w : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) (ib h) (ib h) = 1
          from w.2.2 (ib h), mul_one]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with hlt | hgt
        · have hk' : (k : ℕ) < p + 1 := hlt
          rcases Nat.lt_or_ge (k : ℕ) p with h1 | h1
          · have hz : Nm (ia h) k = 0 := hNu h1
            rw [hz, zero_mul]
          · have hke : k = ia h := Fin.ext (by simp only [ia]; omega)
            rw [hke, hNd, zero_mul]
        · have hz : ((w : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) k (ib h) = 0 :=
            w.2.1 hgt
          rw [hz, mul_zero]
      · simp
    have hd := hasDerivAt_blockFourierCoefficient_comp h hφ hα hγc hAu hγ' j
    refine hd.congr_deriv ?_
    rw [hδ, hAd, hAd, hApq]
    simp only [hAd, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
    ring
  have h0' : ∀ j ∈ window m, F j 0 = 0 := fun j hj => by
    simp only [F, hγ0]
    exact h0 j hj
  intro j hj
  have := window_ode _ _ _ hF h0' zero_le_one j hj
  simpa only [F, hγ1] using this

/-- Vanishing on the window propagates from `g` to `exp(diag l) g`, along the path
`t ↦ exp(t diag l) g` with velocity `diag(l) γ(t)`. -/
theorem window_eq_zero_expDiagonal_mul (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    {m : ℕ} (hδ : α (ia h) - α (ib h) = m + 1) (l : Fin N → ℝ)
    (g : Langlands.GeneralLinear N ℝ)
    (h0 : ∀ j ∈ window m, blockFourierCoefficient N p j φ g = 0) :
    ∀ j ∈ window m,
      blockFourierCoefficient N p j φ (matrixExpUnit N (Matrix.diagonal l) * g) = 0 := by
  set L : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal l with hL
  set γ : ℝ → Langlands.GeneralLinear N ℝ := fun t => matrixExpUnit N (t • L) * g with hγ
  have hγv : ∀ t, (γ t : Matrix (Fin N) (Fin N) ℝ) =
      NormedSpace.exp (t • L) * (g : Matrix (Fin N) (Fin N) ℝ) := fun t => by
    rw [hγ, Units.val_mul, matrixExpUnit_val]
  have hγ0 : γ 0 = g := by
    simp only [hγ, zero_smul, matrixExpUnit_zero, one_mul]
  have hγ1 : γ 1 = matrixExpUnit N L * g := by
    simp only [hγ, one_smul]
  have hγc : ContDiff ℝ 1 fun t => (γ t : Matrix (Fin N) (Fin N) ℝ) := by
    have e : (fun t => (γ t : Matrix (Fin N) (Fin N) ℝ)) =
        fun t : ℝ => NormedSpace.exp (t • L) * (g : Matrix (Fin N) (Fin N) ℝ) := funext hγv
    rw [e]
    exact ((RealJacquetFrobenius.contDiff_matExp.of_le (mod_cast le_top)).comp
      (contDiff_id.smul contDiff_const)).mul contDiff_const
  have hLu : L.IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hLd : ∀ i, L i i = l i := fun i => Matrix.diagonal_apply_eq _ _
  have hLpq : L (ia h) (ib h) = 0 := Matrix.diagonal_apply_ne _ (ia_ne_ib h)
  set x : ℂ := ((l (ia h) : ℝ) : ℂ) - ((l (ib h) : ℝ) : ℂ) with hx
  let F : ℤ → ℝ → ℂ := fun j t => blockFourierCoefficient N p j φ (γ t)
  have hF : ∀ j ∈ window m, ∀ t : ℝ, HasDerivAt (F j)
      ((∑ i, α i * ((l i : ℝ) : ℂ) - ((m : ℂ) + 1) * x / 2) * F j t +
        (x / 4) * ((m : ℂ) + 1 + j - 2) * F (j - 2) t +
        (x / 4) * ((m : ℂ) + 1 - j - 2) * F (j + 2) t) t := by
    intro j _ t
    have hγ' : HasDerivAt (fun s => (γ s : Matrix (Fin N) (Fin N) ℝ))
        (L * (γ t : Matrix (Fin N) (Fin N) ℝ)) t := by
      have e : (fun t => (γ t : Matrix (Fin N) (Fin N) ℝ)) =
          fun t : ℝ => NormedSpace.exp (t • L) * (g : Matrix (Fin N) (Fin N) ℝ) := funext hγv
      rw [e]
      refine ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) L t).mul_const
        (g : Matrix (Fin N) (Fin N) ℝ)).congr_deriv ?_
      rw [hγv, mul_assoc]
    have hd := hasDerivAt_blockFourierCoefficient_comp h hφ hα hγc hLu hγ' j
    refine hd.congr_deriv ?_
    rw [hδ, hLpq]
    simp only [hLd, hx, Complex.ofReal_zero, mul_zero, sub_zero, add_zero]
    ring
  have h0' : ∀ j ∈ window m, F j 0 = 0 := fun j hj => by
    simp only [F, hγ0]
    exact h0 j hj
  intro j hj
  have := window_ode _ _ _ hF h0' zero_le_one j hj
  simpa only [F, hγ1] using this

/-! ## The Iwasawa decomposition with positive diagonal -/

/-- Every `g ∈ GL_N(ℝ)` is `exp(diag l) u k` with `u` upper unipotent and `k ∈ O(N)`. -/
theorem exists_expDiagonal_mul_upperUnipotent_mul_unitaryCompact
    (g : Langlands.GeneralLinear N ℝ) :
    ∃ (l : Fin N → ℝ) (u : upperUnipotent N ℝ) (k : Langlands.GeneralLinear N ℝ),
      k ∈ unitaryCompact ℝ N ∧
        g = matrixExpUnit N (Matrix.diagonal l) * ((u : Langlands.GeneralLinear N ℝ) * k) := by
  obtain ⟨b, w, hb, hbu, hw, hg⟩ :=
    Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary
      (g : Matrix (Fin N) (Fin N) ℝ) g.isUnit
  have hdiag : ∀ i, b i i ≠ 0 := by
    have h0 : b.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det b).mp hbu).ne_zero
    rw [Matrix.det_of_isUpperTriangular hb] at h0
    exact fun i => Finset.prod_ne_zero_iff.mp h0 i (Finset.mem_univ i)
  set s : Fin N → ℝ := fun i => if 0 < b i i then 1 else -1 with hs
  have hs2 : ∀ i, s i * s i = 1 := fun i => by
    simp only [hs]
    split_ifs <;> norm_num
  have hbs : ∀ i, b i i * s i = |b i i| := fun i => by
    simp only [hs]
    split_ifs with hpos
    · rw [mul_one, abs_of_pos hpos]
    · rw [mul_neg_one, abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) (hdiag i))]
  set S : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal s with hS
  have hSS : S * S = 1 := by
    rw [hS, Matrix.diagonal_mul_diagonal]
    simp only [hs2]
    exact Matrix.diagonal_one
  have hSu : S ∈ Matrix.unitaryGroup (Fin N) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hst : star S = S := by
      rw [hS, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [hst, hSS]
  set l : Fin N → ℝ := fun i => Real.log |b i i| with hl
  set E : Langlands.GeneralLinear N ℝ := matrixExpUnit N (Matrix.diagonal l) with hE
  set Sg : Langlands.GeneralLinear N ℝ := Unitary.toUnits ⟨S, hSu⟩ with hSg
  set B : Langlands.GeneralLinear N ℝ := hbu.unit with hB
  set uG : Langlands.GeneralLinear N ℝ := E⁻¹ * B * Sg with huG
  have hEinv : ((E⁻¹ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.diagonal fun i => |b i i|⁻¹ := by
    rw [hE, matrixExpUnit_diagonal, ← map_inv, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val]
    congr 1
    funext i
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_mk0, hl,
      Real.exp_log (abs_pos.mpr (hdiag i))]
  have hBv : (B : Matrix (Fin N) (Fin N) ℝ) = b := hbu.unit_spec
  have hSv : (Sg : Matrix (Fin N) (Fin N) ℝ) = S := rfl
  have huv : (uG : Matrix (Fin N) (Fin N) ℝ) = Matrix.diagonal (fun i => |b i i|⁻¹) * b * S := by
    rw [huG, Units.val_mul, Units.val_mul, hEinv, hBv, hSv]
  have hu : uG ∈ upperUnipotent N ℝ := by
    refine ⟨?_, fun i => ?_⟩
    · change (uG : Matrix (Fin N) (Fin N) ℝ).BlockTriangular id
      rw [huv]
      exact ((Matrix.blockTriangular_diagonal _).mul hb).mul (Matrix.blockTriangular_diagonal _)
    · change (uG : Matrix (Fin N) (Fin N) ℝ) i i = 1
      rw [huv, hS, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc, hbs,
        inv_mul_cancel₀ (abs_pos.mpr (hdiag i)).ne']
  set k : Langlands.GeneralLinear N ℝ :=
    Unitary.toUnits ⟨S * w, Submonoid.mul_mem _ hSu hw⟩ with hk
  have hkv : (k : Matrix (Fin N) (Fin N) ℝ) = S * w := rfl
  refine ⟨l, ⟨uG, hu⟩, k, Submonoid.mul_mem _ hSu hw, ?_⟩
  apply Units.ext
  change (g : Matrix (Fin N) (Fin N) ℝ) = ((E * (uG * k) : Langlands.GeneralLinear N ℝ) :
    Matrix (Fin N) (Fin N) ℝ)
  rw [huG, mul_assoc, mul_assoc, mul_inv_cancel_left, Units.val_mul, Units.val_mul, hBv,
    hSv, hkv, ← mul_assoc S S w, hSS, one_mul, hg]

/-! ## Propagation -/

/-- **Propagation.** Let `φ` be smooth with `IsExpEquivariant α φ` and `α_p - α_{p+1} = m + 1`.
If `Φ_j(φ)(k) = 0` for all `k ∈ O(N)` and all `j` in the window `|j| < m`, `j ≡ m + 1 (mod 2)`,
then `Φ_j(φ)(g) = 0` for all `g ∈ GL_N(ℝ)` and these `j`. -/
theorem blockFourierCoefficient_window_eq_zero (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    {m : ℕ} (hδ : α (ia h) - α (ib h) = m + 1)
    (hK : ∀ k ∈ unitaryCompact ℝ N, ∀ j ∈ window m, blockFourierCoefficient N p j φ k = 0)
    (g : Langlands.GeneralLinear N ℝ) :
    ∀ j ∈ window m, blockFourierCoefficient N p j φ g = 0 := by
  obtain ⟨l, u, k, hk, rfl⟩ := exists_expDiagonal_mul_upperUnipotent_mul_unitaryCompact g
  exact window_eq_zero_expDiagonal_mul h hφ hα hδ l _
    (window_eq_zero_upperUnipotent_mul h hφ hα hδ u k (hK k hk))

end RealBlockPropagation

end Langlands.Archimedean
