import Langlands.Representation.Archimedean.RealSwapFLanding
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Polynomial.Roots

/-!
# Landing of block multiplier composites: reduction to special parameters

See the companion Markdown file.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory

namespace Langlands.Archimedean

namespace RealSwapLandingAlgebra

open RealBlockFourierFinite RealBlockJacquet RealBlockMultiplier RealSwapFLanding
open Langlands.LocalFactor.Archimedean
open RealBlockRotation

variable {N : ℕ}

/-! ## Fourier uniqueness for continuous functions -/

/-- A continuous `2π`-periodic function all of whose Fourier coefficients vanish vanishes
at `0`. -/
theorem eq_zero_of_coeff_eq_zero {F : ℝ → ℂ} (hF : Continuous F)
    (hper : Function.Periodic F (2 * Real.pi)) (h0 : ∀ k : ℤ, coeff k F = 0) : F 0 = 0 := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hc : Continuous (AddCircle.liftIco (2 * Real.pi) 0 F) :=
    AddCircle.liftIco_continuous (by rw [zero_add]; exact (hper 0).symm.trans (by rw [zero_add]))
      hF.continuousOn
  set Fc : C(AddCircle (2 * Real.pi), ℂ) := ⟨_, hc⟩ with hFc
  have hval : ∀ x : ℝ, x ∈ Set.Ico 0 (2 * Real.pi) → Fc (x : AddCircle (2 * Real.pi)) = F x :=
    fun x hx => AddCircle.liftIco_coe_apply (by rw [zero_add]; exact hx)
  have hcoeff : ∀ n : ℤ, fourierCoeff Fc n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0]
    have e : (∫ x in (0 : ℝ)..0 + 2 * Real.pi,
        fourier (-n) (x : AddCircle (2 * Real.pi)) • Fc (x : AddCircle (2 * Real.pi))) =
        coeff n F := by
      rw [zero_add, coeff]
      refine intervalIntegral.integral_congr_Ioo_of_le (by positivity) fun x hx => ?_
      simp only [smul_eq_mul]
      rw [hval x ⟨hx.1.le, hx.2⟩, fourier_coe_apply, mul_comm]
      congr 2
      push_cast
      field_simp
    rw [e, h0 n, smul_zero]
  have hsum := hasSum_fourier_series_of_summable (f := Fc)
    (by rw [show fourierCoeff Fc = 0 from funext hcoeff]; exact summable_zero)
  simp only [hcoeff, zero_smul] at hsum
  have hz : Fc = 0 := hsum.unique hasSum_zero
  have h1 := hval 0 ⟨le_rfl, by positivity⟩
  rw [hz] at h1
  simpa using h1.symm

theorem coeff_sub {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) (k : ℤ) :
    coeff k (fun θ => F θ - G θ) = coeff k F - coeff k G := by
  unfold coeff
  simp only [sub_mul]
  exact intervalIntegral.integral_sub (intervalIntegrable_coeff hF k _ _)
    (intervalIntegrable_coeff hG k _ _)

/-- **Fourier uniqueness at a point.** Two continuous functions with the same block Fourier
coefficients at `g` agree at `g`. -/
theorem eq_of_blockFourierCoefficient_eq {p : ℕ} (hp : p + 1 < N)
    {F G : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (g : Langlands.GeneralLinear N ℝ)
    (h : ∀ k : ℤ, blockFourierCoefficient N p k F g = blockFourierCoefficient N p k G g) :
    F g = G g := by
  have hF' : Continuous fun θ : ℝ => F (blockRotation N p θ * g) :=
    hF.comp ((continuous_blockRotation N p).mul continuous_const)
  have hG' : Continuous fun θ : ℝ => G (blockRotation N p θ * g) :=
    hG.comp ((continuous_blockRotation N p).mul continuous_const)
  have key := eq_zero_of_coeff_eq_zero (F := fun θ => F (blockRotation N p θ * g) -
      G (blockRotation N p θ * g)) (hF'.sub hG')
    (fun θ => by simp only [blockRotation_add_two_pi hp])
    (fun k => by
      rw [coeff_sub hF' hG', ← blockFourierCoefficient_eq_coeff,
        ← blockFourierCoefficient_eq_coeff, h k, sub_self])
  simpa [blockRotation_zero, sub_eq_zero] using key

/-! ## Linearity of block Fourier coefficients -/

theorem blockFourierCoefficient_sum {ι : Type*} (p : ℕ) (k : ℤ) (I : Finset ι)
    (F : ι → Langlands.GeneralLinear N ℝ → ℂ) (hF : ∀ i ∈ I, Continuous (F i))
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k (fun x => ∑ i ∈ I, F i x) g =
      ∑ i ∈ I, blockFourierCoefficient N p k (F i) g := by
  unfold blockFourierCoefficient
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i hi =>
    intervalIntegrable_blockFourier (hF i hi) p k g _ _

theorem blockFourierCoefficient_const_mul (p : ℕ) (k : ℤ) (c : ℂ)
    (F : Langlands.GeneralLinear N ℝ → ℂ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k (fun x => c * F x) g = c * blockFourierCoefficient N p k F g :=
  blockFourierCoefficient_smul p k c F g

/-- **Modes of a block trigonometric sum.** For continuous `F`,
`Φ_j (Σ_{i ∈ I} c_i Φ_i F) (x) = 2π c_j Φ_j F (x)` if `j ∈ I` and `0` otherwise. -/
theorem blockFourierCoefficient_sum_modes {p : ℕ} (hp : p + 1 < N) (I : Finset ℤ) (c : ℤ → ℂ)
    (F : Langlands.GeneralLinear N ℝ → ℂ) (j : ℤ) (x : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p j (fun y => ∑ i ∈ I, c i * blockFourierCoefficient N p i F y) x =
      if j ∈ I then c j * blockFourierCoefficient N p j F x * (2 * (Real.pi : ℂ)) else 0 := by
  rw [blockFourierCoefficient_eq_coeff N p j]
  have e : (fun θ : ℝ => (fun y => ∑ i ∈ I, c i * blockFourierCoefficient N p i F y)
      (blockRotation N p θ * x)) =
      fun θ => ∑ i ∈ I, (c i * blockFourierCoefficient N p i F x) * expMode i θ := by
    funext θ
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [blockFourierCoefficient_blockRotation_mul hp, expMode]
    ring
  rw [e, coeff_finset_sum_expMode]

/-! ## Recurrent symmetric multipliers on a window -/

/-- The polynomial `∏_{r < m} (ε + 2r + 2 - X) · ∏_{m ≤ r < M} (X + ε + 2r)`. On the window
`m ≤ M` its values at `δ` span the solutions of the recurrence for `δ` on the parity class
`ε` (`exists_eq_windowPoly`). -/
def windowPoly (ε : ℤ) (M m : ℕ) : Polynomial ℂ :=
  (∏ r ∈ Finset.range m, (Polynomial.C ((ε : ℂ) + 2 * (r : ℂ) + 2) - Polynomial.X)) *
    ∏ r ∈ Finset.Ico m M, (Polynomial.X + Polynomial.C ((ε : ℂ) + 2 * (r : ℂ)))

theorem eval_windowPoly (ε : ℤ) (M m : ℕ) (δ : ℂ) :
    (windowPoly ε M m).eval δ =
      (∏ r ∈ Finset.range m, ((ε : ℂ) + 2 * (r : ℂ) + 2 - δ)) *
        ∏ r ∈ Finset.Ico m M, (δ + ((ε : ℂ) + 2 * (r : ℂ))) := by
  simp [windowPoly, Polynomial.eval_prod]

theorem windowPoly_succ (ε : ℤ) {M m : ℕ} (hm : m < M) (δ : ℂ) :
    (windowPoly ε M (m + 1)).eval δ * (δ + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - δ) * (windowPoly ε M m).eval δ := by
  rw [eval_windowPoly, eval_windowPoly, Finset.prod_range_succ,
    Finset.prod_eq_prod_Ico_succ_bot hm]
  ring

/-- **Window lemma.** A solution of the recurrence for `δ` on the parity class `ε ∈ {0, 1}` is,
on `ε, ε + 2, …, ε + 2M`, a multiple of the values of `windowPoly`. -/
theorem exists_eq_windowPoly {δ : ℂ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1) {μ : ℤ → ℂ}
    (hrec : IsRecurrent δ ε μ) (M : ℕ) :
    ∃ c : ℂ, ∀ m : ℕ, m ≤ M → μ (ε + 2 * m) = c * (windowPoly ε M m).eval δ := by
  have hstep : ∀ m : ℕ, μ (ε + 2 * (m + 1 : ℕ)) * (δ + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - δ) * μ (ε + 2 * m) := by
    intro m
    have h := hrec (ε + 2 * m) ⟨m, by ring⟩
    rw [show ε + 2 * (m : ℤ) + 2 = ε + 2 * ((m + 1 : ℕ) : ℤ) by push_cast; ring] at h
    push_cast at h ⊢
    linear_combination h
  by_cases hA : ∀ r : ℕ, r < M → δ + ε + 2 * r ≠ 0
  · -- forward recursion from `m = 0`
    have hP0 : (windowPoly ε M 0).eval δ ≠ 0 := by
      rw [eval_windowPoly, Finset.range_zero, Finset.prod_empty, one_mul,
        Finset.prod_ne_zero_iff]
      intro r hr
      rw [← add_assoc]
      exact hA r (Finset.mem_Ico.mp hr).2
    refine ⟨μ ε / (windowPoly ε M 0).eval δ, fun m hm => ?_⟩
    induction m with
    | zero => simp [hP0]
    | succ m ih =>
        have ih := ih (by omega)
        have ha := hA m (by omega)
        have h1 := hstep m
        have h2 := windowPoly_succ ε (show m < M by omega) δ
        apply mul_right_cancel₀ ha
        rw [h1, ih, mul_assoc, h2]
        ring
  · -- backward recursion from `m = M`
    push Not at hA
    obtain ⟨r₀, hr₀, hδ⟩ := hA
    have hB : ∀ m : ℕ, (ε : ℂ) + 2 * m + 2 - δ ≠ 0 := by
      intro m
      have hδ' : δ = -((ε : ℂ) + 2 * r₀) := by linear_combination hδ
      rw [hδ']
      have : ((ε : ℂ) + 2 * m + 2 + (ε + 2 * r₀)) = ((2 * ε + 2 * m + 2 + 2 * r₀ : ℤ) : ℂ) := by
        push_cast; ring
      rw [sub_neg_eq_add, this, Int.cast_ne_zero]
      rcases hε with h | h <;> subst h <;> omega
    have hPM : (windowPoly ε M M).eval δ ≠ 0 := by
      rw [eval_windowPoly, Finset.Ico_self, Finset.prod_empty, mul_one, Finset.prod_ne_zero_iff]
      exact fun r _ => hB r
    refine ⟨μ (ε + 2 * M) / (windowPoly ε M M).eval δ, ?_⟩
    have key : ∀ t : ℕ, t ≤ M → μ (ε + 2 * ((M - t : ℕ) : ℤ)) =
        μ (ε + 2 * M) / (windowPoly ε M M).eval δ * (windowPoly ε M (M - t)).eval δ := by
      intro t ht
      induction t with
      | zero => simp [hPM]
      | succ t ih =>
          have ih := ih (by omega)
          set m := M - (t + 1) with hm
          have hm1 : M - t = m + 1 := by omega
          rw [hm1] at ih
          have h1 := hstep m
          have h2 := windowPoly_succ ε (show m < M by omega) δ
          apply mul_left_cancel₀ (hB m)
          rw [← h1, ih]
          linear_combination (μ (ε + 2 * M) / (windowPoly ε M M).eval δ) * h2
    intro m hm
    have := key (M - m) (by omega)
    rwa [show M - (M - m) = m by omega] at this

/-! ## Extension of the window values to negative indices -/

/-- The polynomial attached to the index `i`: on the class `i ≡ ε (mod 2)` it is
`windowPoly ε M m` for `i = ε + 2m ≥ 0` and `σ · windowPoly ε M m` for `i = -(ε + 2m) < 0`;
off the class it is `0`. -/
def extPoly (ε : ℤ) (σ : ℂ) (M : ℕ) (i : ℤ) : Polynomial ℂ :=
  if Even (i - ε) then
    (if 0 ≤ i then windowPoly ε M ((i - ε) / 2).toNat
      else Polynomial.C σ * windowPoly ε M ((-i - ε) / 2).toNat)
  else 0

/-- **Symmetric window lemma.** A solution of the recurrence for `δ` on the class `ε ∈ {0, 1}`
which is symmetric with sign `σ` is, on the indices `|i| ≤ ε + 2M` of the class, a multiple
`c` of the values of `extPoly` at `δ`; `c ≠ 0` if the solution does not vanish at `ε`. -/
theorem exists_eq_extPoly {δ : ℂ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1) {σ : ℂ} {μ : ℤ → ℂ}
    (hrec : IsRecurrent δ ε μ) (hsym : IsSymmetric ε σ μ) (M : ℕ) :
    ∃ c : ℂ, (μ ε ≠ 0 → c ≠ 0) ∧ ∀ i : ℤ, Even (i - ε) → |i| ≤ ε + 2 * M →
      μ i = c * (extPoly ε σ M i).eval δ := by
  obtain ⟨c, hc⟩ := exists_eq_windowPoly hε hrec M
  refine ⟨c, fun h0 hc0 => h0 ?_, fun i hi hiM => ?_⟩
  · have h := hc 0 (Nat.zero_le _)
    rw [hc0, zero_mul] at h
    simpa using h
  · obtain ⟨r, hr⟩ := hi
    rw [abs_le] at hiM
    unfold extPoly
    simp only [show Even (i - ε) from ⟨r, hr⟩, ↓reduceIte]
    split_ifs with hpos
    · have hm : i = ε + 2 * (((i - ε) / 2).toNat : ℕ) := by
        rcases hε with h | h <;> subst h <;> omega
      have hmM : ((i - ε) / 2).toNat ≤ M := by
        rcases hε with h | h <;> subst h <;> omega
      have hμ : μ i = c * (windowPoly ε M ((i - ε) / 2).toNat).eval δ := by
        conv_lhs => rw [hm]
        exact hc _ hmM
      exact hμ
    · have hm : -i = ε + 2 * (((-i - ε) / 2).toNat : ℕ) := by
        rcases hε with h | h <;> subst h <;> omega
      have hmM : ((-i - ε) / 2).toNat ≤ M := by
        rcases hε with h | h <;> subst h <;> omega
      have hμ : μ (-i) = c * (windowPoly ε M ((-i - ε) / 2).toNat).eval δ := by
        conv_lhs => rw [hm]
        exact hc _ hmM
      have hs := hsym (-i) ⟨-r - ε, by omega⟩
      rw [neg_neg] at hs
      rw [hs, hμ, Polynomial.eval_mul, Polynomial.eval_C]
      ring

/-! ## Bilinear window sums -/

/-- The polynomial `Σ_{j ∈ I₀} extPoly₀ j (X + ℓ) · Σ_{i ∈ I₁} extPoly₁ i (X) · B i j`. -/
def windowSumPoly (ε₀ ε₁ : ℤ) (σ₀ σ₁ ℓ : ℂ) (M₀ M₁ : ℕ) (I₀ I₁ : Finset ℤ)
    (B : ℤ → ℤ → ℂ) : Polynomial ℂ :=
  ∑ j ∈ I₀, (extPoly ε₀ σ₀ M₀ j).comp (Polynomial.X + Polynomial.C ℓ) *
    ∑ i ∈ I₁, extPoly ε₁ σ₁ M₁ i * Polynomial.C (B i j)

theorem eval_windowSumPoly (ε₀ ε₁ : ℤ) (σ₀ σ₁ ℓ : ℂ) (M₀ M₁ : ℕ) (I₀ I₁ : Finset ℤ)
    (B : ℤ → ℤ → ℂ) (δ : ℂ) :
    (windowSumPoly ε₀ ε₁ σ₀ σ₁ ℓ M₀ M₁ I₀ I₁ B).eval δ =
      ∑ j ∈ I₀, (extPoly ε₀ σ₀ M₀ j).eval (δ + ℓ) *
        ∑ i ∈ I₁, (extPoly ε₁ σ₁ M₁ i).eval δ * B i j := by
  simp only [windowSumPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- **Window sums.** Let `B i j` vanish for `i` off the class `ε₁`, and let the sums
`Σ_i ν i B i j` vanish for `j` off the class `ε₀` whenever `ν` is symmetric on the class `ε₁`.
Then for multipliers solving the recurrences for `δ` (class `ε₁`) and `δ + ℓ` (class `ε₀`),
symmetric with signs `σ₁`, `σ₀`, the window sum `Σ_j ν₀ j Σ_i ν₁ i B i j` is a multiple of
`windowSumPoly` at `δ`, by a factor that is nonzero when `ν₀ ε₀ ≠ 0` and `ν₁ ε₁ ≠ 0`. -/
theorem window_sum_eq {ε₀ ε₁ : ℤ} (hε₀ : ε₀ = 0 ∨ ε₀ = 1) (hε₁ : ε₁ = 0 ∨ ε₁ = 1)
    {σ₀ σ₁ δ ℓ : ℂ} {M₀ M₁ : ℕ} {I₀ I₁ : Finset ℤ}
    (hI₀ : ∀ j ∈ I₀, |j| ≤ ε₀ + 2 * M₀) (hI₁ : ∀ i ∈ I₁, |i| ≤ ε₁ + 2 * M₁)
    (B : ℤ → ℤ → ℂ) (hB₁ : ∀ i j : ℤ, ¬ Even (i - ε₁) → B i j = 0)
    (hB₀ : ∀ ν : ℤ → ℂ, IsSymmetric ε₁ σ₁ ν → ∀ j : ℤ, ¬ Even (j - ε₀) →
      ∑ i ∈ I₁, ν i * B i j = 0)
    {ν₀ ν₁ : ℤ → ℂ} (hr₁ : IsRecurrent δ ε₁ ν₁) (hs₁ : IsSymmetric ε₁ σ₁ ν₁)
    (hr₀ : IsRecurrent (δ + ℓ) ε₀ ν₀) (hs₀ : IsSymmetric ε₀ σ₀ ν₀) :
    ∃ c₀ c₁ : ℂ, (ν₀ ε₀ ≠ 0 → c₀ ≠ 0) ∧ (ν₁ ε₁ ≠ 0 → c₁ ≠ 0) ∧
      ∑ j ∈ I₀, ν₀ j * ∑ i ∈ I₁, ν₁ i * B i j =
        c₀ * c₁ * (windowSumPoly ε₀ ε₁ σ₀ σ₁ ℓ M₀ M₁ I₀ I₁ B).eval δ := by
  obtain ⟨c₁, hc₁0, hc₁⟩ := exists_eq_extPoly hε₁ hr₁ hs₁ M₁
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_eq_extPoly hε₀ hr₀ hs₀ M₀
  refine ⟨c₀, c₁, hc₀0, hc₁0, ?_⟩
  have hS : ∀ j : ℤ, ∑ i ∈ I₁, ν₁ i * B i j =
      c₁ * ∑ i ∈ I₁, (extPoly ε₁ σ₁ M₁ i).eval δ * B i j := by
    intro j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hev : Even (i - ε₁)
    · rw [hc₁ i hev (hI₁ i hi)]
      ring
    · rw [hB₁ i j hev]
      ring
  rw [eval_windowSumPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hev : Even (j - ε₀)
  · rw [hc₀ j hev (hI₀ j hj), hS j]
    ring
  · rw [hB₀ ν₁ hs₁ j hev]
    simp [extPoly, hev]

/-- A polynomial vanishing at all `n + 2`, `n ∈ ℕ`, vanishes everywhere. -/
theorem eval_eq_zero_of_nat {P : Polynomial ℂ} (h : ∀ n : ℕ, P.eval ((n : ℂ) + 2) = 0)
    (δ : ℂ) : P.eval δ = 0 := by
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Set.range fun n : ℕ => (n : ℂ) + 2) ?_ ?_
    · rintro _ ⟨n, rfl⟩
      exact h n
    · exact Set.infinite_range_of_injective fun a b hab => by simpa using hab
  rw [hP, Polynomial.eval_zero]

/-! ## Expansion of a composite of two block multipliers -/

theorem blockFourierCoefficient_lincomb {ι : Type*} (p : ℕ) (k : ℤ) (I : Finset ι) (c : ι → ℂ)
    (F : ι → Langlands.GeneralLinear N ℝ → ℂ) (hF : ∀ i ∈ I, Continuous (F i))
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k (fun x => ∑ i ∈ I, c i * F i x) g =
      ∑ i ∈ I, c i * blockFourierCoefficient N p k (F i) g :=
  (blockFourierCoefficient_sum p k I (fun i x => c i * F i x)
    (fun i hi => continuous_const.mul (hF i hi)) g).trans
    (Finset.sum_congr rfl fun i _ => blockFourierCoefficient_const_mul p k (c i) (F i) g)

theorem blockFourierCoefficient_zero_fun (p : ℕ) (k : ℤ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k (fun _ => 0) g = 0 := by
  simp [blockFourierCoefficient]

/-- **Expansion.** Let `f` be continuous with block modes along `r_p` supported in
`|i| ≤ D₁` on `O(N)`, and the modes along `r_q` of each `Φ^p_i f`, `|i| ≤ D₁`, supported in
`|j| ≤ D₀` on `O(N)`. If `h`, `u` are continuous with `Φ^p_k h = μ₁ k Φ^p_k f` and
`Φ^q_k u = μ₀ k Φ^q_k h` on `O(N)`, then for every block `r` and `g ∈ O(N)`,
`Φ^r_k u (g) = (2π)⁻² Σ_{|j| ≤ D₀} μ₀ j Σ_{|i| ≤ D₁} μ₁ i Φ^r_k Φ^q_j Φ^p_i f (g)`. -/
theorem expansion {p q : ℕ} (hp : p + 1 < N) (hq : q + 1 < N)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f) {D₀ D₁ : ℕ}
    (hD₁ : ∀ i : ℤ, (D₁ : ℤ) < |i| → ∀ g ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p i f g = 0)
    (hD₀ : ∀ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, ∀ j : ℤ, (D₀ : ℤ) < |j| →
      ∀ g ∈ unitaryCompact ℝ N,
        blockFourierCoefficient N q j (blockFourierCoefficient N p i f) g = 0)
    {μ₀ μ₁ : ℤ → ℂ} {h u : Langlands.GeneralLinear N ℝ → ℂ} (hh : Continuous h)
    (hu : Continuous u)
    (h₁ : ∀ g ∈ unitaryCompact ℝ N, ∀ k : ℤ,
      blockFourierCoefficient N p k h g = μ₁ k * blockFourierCoefficient N p k f g)
    (h₀ : ∀ g ∈ unitaryCompact ℝ N, ∀ k : ℤ,
      blockFourierCoefficient N q k u g = μ₀ k * blockFourierCoefficient N q k h g)
    (r : ℕ) (k : ℤ) {g : Langlands.GeneralLinear N ℝ} (hg : g ∈ unitaryCompact ℝ N) :
    blockFourierCoefficient N r k u g =
      (2 * (Real.pi : ℂ))⁻¹ * (2 * (Real.pi : ℂ))⁻¹ *
        ∑ j ∈ Finset.Icc (-(D₀ : ℤ)) D₀, μ₀ j * ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, μ₁ i *
          blockFourierCoefficient N r k
            (blockFourierCoefficient N q j (blockFourierCoefficient N p i f)) g := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hc2 : (2 * (Real.pi : ℂ))⁻¹ * (2 * (Real.pi : ℂ)) = 1 := inv_mul_cancel₀ hπ
  have hcont : ∀ i : ℤ, Continuous (blockFourierCoefficient N p i f) :=
    fun i => continuous_blockFourierCoefficient p i hf
  have hcont' : ∀ i j : ℤ,
      Continuous (blockFourierCoefficient N q j (blockFourierCoefficient N p i f)) :=
    fun i j => continuous_blockFourierCoefficient q j (hcont i)
  obtain ⟨h', hh'⟩ : ∃ h' : Langlands.GeneralLinear N ℝ → ℂ, h' = fun x =>
      ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁,
        ((2 * (Real.pi : ℂ))⁻¹ * μ₁ i) * blockFourierCoefficient N p i f x := ⟨_, rfl⟩
  have hh'c : Continuous h' := by
    rw [hh']
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hcont i)
  have hhK : ∀ x ∈ unitaryCompact ℝ N, h x = h' x := by
    intro x hx
    refine eq_of_blockFourierCoefficient_eq hp hh hh'c x fun j => ?_
    rw [hh', blockFourierCoefficient_sum_modes hp _ (fun i => (2 * (Real.pi : ℂ))⁻¹ * μ₁ i) f j x,
      h₁ x hx j]
    split_ifs with hj
    · linear_combination (-(μ₁ j * blockFourierCoefficient N p j f x)) * hc2
    · have hj' : (D₁ : ℤ) < |j| := by
        rw [Finset.mem_Icc, ← abs_le] at hj
        exact not_le.mp hj
      rw [hD₁ j hj' x hx, mul_zero]
  have hqh' : ∀ (j : ℤ) (x : Langlands.GeneralLinear N ℝ), blockFourierCoefficient N q j h' x =
      ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, ((2 * (Real.pi : ℂ))⁻¹ * μ₁ i) *
        blockFourierCoefficient N q j (blockFourierCoefficient N p i f) x := by
    intro j x
    rw [hh']
    exact blockFourierCoefficient_lincomb q j _ _ _ (fun i _ => hcont i) x
  obtain ⟨u', hu'⟩ : ∃ u' : Langlands.GeneralLinear N ℝ → ℂ, u' = fun x =>
      ∑ j ∈ Finset.Icc (-(D₀ : ℤ)) D₀,
        ((2 * (Real.pi : ℂ))⁻¹ * μ₀ j) * blockFourierCoefficient N q j h' x := ⟨_, rfl⟩
  have hu'c : Continuous u' := by
    rw [hu']
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_blockFourierCoefficient q j hh'c)
  have huK : ∀ x ∈ unitaryCompact ℝ N, u x = u' x := by
    intro x hx
    refine eq_of_blockFourierCoefficient_eq hq hu hu'c x fun j => ?_
    rw [hu', blockFourierCoefficient_sum_modes hq _ (fun j => (2 * (Real.pi : ℂ))⁻¹ * μ₀ j) h' j x,
      h₀ x hx j, blockFourierCoefficient_congr hhK q j hx]
    split_ifs with hj
    · linear_combination (-(μ₀ j * blockFourierCoefficient N q j h' x)) * hc2
    · have hj' : (D₀ : ℤ) < |j| := by
        rw [Finset.mem_Icc, ← abs_le] at hj
        exact not_le.mp hj
      rw [hqh' j x, Finset.sum_eq_zero fun i hi => by rw [hD₀ i hi j hj' x hx, mul_zero],
        mul_zero]
  have e : ∀ j : ℤ, blockFourierCoefficient N r k (blockFourierCoefficient N q j h') g =
      ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, ((2 * (Real.pi : ℂ))⁻¹ * μ₁ i) *
        blockFourierCoefficient N r k
          (blockFourierCoefficient N q j (blockFourierCoefficient N p i f)) g := by
    intro j
    rw [show blockFourierCoefficient N q j h' = fun x => ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁,
        ((2 * (Real.pi : ℂ))⁻¹ * μ₁ i) *
          blockFourierCoefficient N q j (blockFourierCoefficient N p i f) x from funext (hqh' j)]
    exact blockFourierCoefficient_lincomb r k _ _ _ (fun i _ => hcont' i j) g
  rw [blockFourierCoefficient_congr huK r k hg, hu',
    blockFourierCoefficient_lincomb r k _ _ _
      (fun j _ => continuous_blockFourierCoefficient q j hh'c) g]
  simp_rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## Parity under the rotation by `π` -/

theorem exp_int_mul_pi (j : ℤ) :
    Complex.exp ((j : ℂ) * (Real.pi : ℂ) * Complex.I) = (-1 : ℂ) ^ j := by
  rw [mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem neg_one_zpow_eq_iff (i e : ℤ) : (-1 : ℂ) ^ i = (-1 : ℂ) ^ e ↔ Even (i - e) := by
  rw [neg_one_zpow_eq_ite, neg_one_zpow_eq_ite, Int.even_sub]
  by_cases h1 : Even i <;> by_cases h2 : Even e <;> simp [h1, h2] <;> norm_num

theorem even_sub_iff_mod_two (k e : ℤ) : Even (k - e) ↔ Even (k - e % 2) := by
  simp only [Int.even_iff]
  omega

theorem isRecurrent_mod_two {δ : ℂ} {e : ℤ} {μ : ℤ → ℂ} (h : IsRecurrent δ e μ) :
    IsRecurrent δ (e % 2) μ :=
  fun k hk => h k ((even_sub_iff_mod_two k e).mpr hk)

theorem isSymmetric_mod_two {e : ℤ} {σ : ℂ} {μ : ℤ → ℂ} (h : IsSymmetric e σ μ) :
    IsSymmetric (e % 2) σ μ :=
  fun k hk => h k ((even_sub_iff_mod_two k e).mpr hk)

/-- If `F (r_p(π) y) = τ F(y)` for all `y`, the modes `Φ^p_j F` vanish unless `(-1)^j = τ`. -/
theorem blockFourierCoefficient_eq_zero_of_rotation_pi {p : ℕ} (hp : p + 1 < N)
    {F : Langlands.GeneralLinear N ℝ → ℂ} {τ : ℂ}
    (hF : ∀ y, F (blockRotation N p Real.pi * y) = τ * F y) {j : ℤ} (hj : (-1 : ℂ) ^ j ≠ τ)
    (x : Langlands.GeneralLinear N ℝ) : blockFourierCoefficient N p j F x = 0 := by
  have h1 := blockFourierCoefficient_blockRotation_mul hp F j Real.pi x
  have h2 : blockFourierCoefficient N p j F (blockRotation N p Real.pi * x) =
      τ * blockFourierCoefficient N p j F x := by
    unfold blockFourierCoefficient
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext θ
    have hc : blockRotation N p θ * (blockRotation N p Real.pi * x) =
        blockRotation N p Real.pi * (blockRotation N p θ * x) := by
      rw [← mul_assoc, ← mul_assoc, ← blockRotation_add, ← blockRotation_add, add_comm]
    rw [hc, hF, mul_assoc]
  rw [exp_int_mul_pi, h2] at h1
  have h3 : ((-1 : ℂ) ^ j - τ) * blockFourierCoefficient N p j F x = 0 := by
    linear_combination -h1
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hj)

/-- **Rotation by `π` along `r_0` of a sum of `r_1`-modes.** For a principal series function
`f` on `GL_3(ℝ)` and coefficients `ν` with `ν(-i) = σ ν(i)` on the parity class of the
`r_1`-modes of `f`, `H = Σ_{|i| ≤ D} ν i Φ¹_i f` satisfies `H(r_0(π) y) = χ₀(-1) χ₁(-1) σ H(y)`. -/
theorem sum_blockFourierCoefficient_rotation_pi {χ : ℕ → ℝˣ → ℂ} (hχ : ∀ i : ℕ, χ i 1 = 1)
    {f : Langlands.GeneralLinear 3 ℝ → ℂ} (hf : f ∈ principalSeries ℝ 3 χ) (D : ℕ)
    (ν : ℤ → ℂ) (σ : ℂ)
    (hν : ∀ i : ℤ, (-1 : ℂ) ^ i = χ 1 (-1) * χ 2 (-1) → ν (-i) = σ * ν i)
    (y : Langlands.GeneralLinear 3 ℝ) :
    ∑ i ∈ Finset.Icc (-(D : ℤ)) D,
        ν i * blockFourierCoefficient 3 1 i f (blockRotation 3 0 Real.pi * y) =
      χ 0 (-1) * χ 1 (-1) * σ *
        ∑ i ∈ Finset.Icc (-(D : ℤ)) D, ν i * blockFourierCoefficient 3 1 i f y := by
  have h01 : 0 + 1 < 3 := by norm_num
  have h12 : 1 + 1 < 3 := by norm_num
  have hs : ∀ i : ℤ, blockFourierCoefficient 3 1 i f (blockRotation 3 0 Real.pi * y) =
      χ 0 (-1) * χ 1 (-1) * blockFourierCoefficient 3 1 (-i) f y := by
    intro i
    rw [blockRotation_pi h01, mul_assoc,
      blockFourierCoefficient_signReflection_mul_of_not_mem h12 hχ hf (ia h01)
        ⟨by simp [ia], by simp [ia]⟩,
      blockFourierCoefficient_signReflection_mul_of_mem h12 hχ hf (ib h01) (Or.inl rfl)]
    show χ 0 (-1) * (χ 1 (-1) * _) = _
    ring
  simp_rw [hs]
  have hre : ∑ i ∈ Finset.Icc (-(D : ℤ)) D,
      ν i * (χ 0 (-1) * χ 1 (-1) * blockFourierCoefficient 3 1 (-i) f y) =
      ∑ i ∈ Finset.Icc (-(D : ℤ)) D,
        ν (-i) * (χ 0 (-1) * χ 1 (-1) * blockFourierCoefficient 3 1 i f y) := by
    refine Finset.sum_nbij' (fun i => -i) (fun i => -i) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    · intro i _
      simp
    · intro i _
      simp
    · intro i _
      simp
  rw [hre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hpar : (-1 : ℂ) ^ i = χ 1 (-1) * χ 2 (-1)
  · rw [hν i hpar]
    ring
  · rw [blockFourierCoefficient_eq_zero_of_parity h12 hχ hf hpar y]
    ring

theorem blockFourierCoefficient_zero_fun' (p : ℕ) (k : ℤ) :
    blockFourierCoefficient N p k (fun _ => (0 : ℂ)) = fun _ => 0 :=
  funext (blockFourierCoefficient_zero_fun p k)

/-! ## Reduction to the special parameters `δ = n + 2` -/

section Reduction

theorem realPositionCharacter_induced_character_zero (c : RealCharacterData)
    (d : ComplexCharacterData) :
    realPositionCharacter [RealBlock.induced d, RealBlock.character c] 0 (-1) =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) := by
  simp [realPositionCharacter, realInducedFirstCharacter]

theorem realPositionCharacter_induced_character_one (c : RealCharacterData)
    (d : ComplexCharacterData) :
    realPositionCharacter [RealBlock.induced d, RealBlock.character c] 1 (-1) = 1 := by
  simp [realPositionCharacter, realInducedSecondCharacter]

theorem realPositionCharacter_induced_character_two (c : RealCharacterData)
    (d : ComplexCharacterData) :
    realPositionCharacter [RealBlock.induced d, RealBlock.character c] 2 (-1) =
      (-1 : ℂ) ^ c.parity.val := by
  show (c.character (-1) : ℂ) = _
  rw [c.character_eq]
  simp

/-- **Landing at the special parameters.** For every `O(3)`-finite function `f` of the standard
module of `[d, c]` and every `n : ℕ` there are multipliers `μ₁`, `μ₀` solving the recurrences and
symmetries of `RealSwapLandingInducedFirstStatement` for `δ = n + 2`, not vanishing at `0` and
`1`, and continuous `h`, `u` with `Φ¹_k h = μ₁ k Φ¹_k f` and `Φ⁰_k u = μ₀ k Φ⁰_k h` on `O(3)`,
such that `Φ¹_k u` vanishes on `O(3)` for `|k| < ℓ`. -/
def SpecialLanding : Prop :=
  ∀ (c : RealCharacterData) (d : ComplexCharacterData) (f : Langlands.GeneralLinear 3 ℝ → ℂ),
    f ∈ kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
      (unitaryCompact ℝ 3) →
    ∀ n : ℕ, ∃ (μ₀ μ₁ : ℤ → ℂ) (h u : Langlands.GeneralLinear 3 ℝ → ℂ),
      IsRecurrent ((n : ℂ) + 2) (c.parity.val : ℤ) μ₁ ∧
      IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) μ₁ ∧
      μ₁ 0 ≠ 0 ∧ μ₁ 1 ≠ 0 ∧
      IsRecurrent ((n : ℂ) + 2 + (d.weight.natAbs : ℂ))
        ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) μ₀ ∧
      IsSymmetric ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
        ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) μ₀ ∧
      μ₀ 0 ≠ 0 ∧ μ₀ 1 ≠ 0 ∧
      Continuous h ∧ Continuous u ∧
      (∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ,
        blockFourierCoefficient 3 1 k h g = μ₁ k * blockFourierCoefficient 3 1 k f g) ∧
      (∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ,
        blockFourierCoefficient 3 0 k u g = μ₀ k * blockFourierCoefficient 3 0 k h g) ∧
      ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
        blockFourierCoefficient 3 1 k u g = 0

/-- The polynomial of `window_sum_eq` for the data of `RealSwapLandingInducedFirstStatement`:
the coefficients are `B i j = Φ¹_k Φ⁰_j Φ¹_i f (g)` on the windows `|i| ≤ D₁`, `|j| ≤ D₀`. -/
def landingPoly (c : RealCharacterData) (d : ComplexCharacterData)
    (f : Langlands.GeneralLinear 3 ℝ → ℂ) (D₀ D₁ : ℕ) (k : ℤ) (g : Langlands.GeneralLinear 3 ℝ) :
    Polynomial ℂ :=
  windowSumPoly (((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2) (c.parity.val : ℤ)
    ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) ((-1 : ℂ) ^ c.parity.val)
    (d.weight.natAbs : ℂ) D₀ D₁ (Finset.Icc (-(D₀ : ℤ)) D₀) (Finset.Icc (-(D₁ : ℤ)) D₁)
    (fun i j => blockFourierCoefficient 3 1 k
      (blockFourierCoefficient 3 0 j (blockFourierCoefficient 3 1 i f)) g)

/-- **The landing coefficient as a polynomial in `δ`.** For the data of
`RealSwapLandingInducedFirstStatement` with mode bounds `D₁` (for `f` along `r_1`) and `D₀`
(for the `Φ¹_i f` along `r_0`), `Φ¹_k u (g) = (2π)⁻² c₀ c₁ · landingPoly (δ)` with `c₀ ≠ 0`,
`c₁ ≠ 0` when the multipliers do not vanish at the base points of their classes. -/
theorem exists_eq_landingPoly (c : RealCharacterData) (d : ComplexCharacterData)
    {f : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
      (unitaryCompact ℝ 3)) {D₀ D₁ : ℕ}
    (hD₁ : ∀ i : ℤ, (D₁ : ℤ) < |i| → ∀ g ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 i f g = 0)
    (hD₀ : ∀ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, ∀ j : ℤ, (D₀ : ℤ) < |j| →
      ∀ g ∈ unitaryCompact ℝ 3,
        blockFourierCoefficient 3 0 j (blockFourierCoefficient 3 1 i f) g = 0)
    {δ : ℂ} {μ₀ μ₁ : ℤ → ℂ} {h u : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hr₁ : IsRecurrent δ (c.parity.val : ℤ) μ₁)
    (hs₁ : IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) μ₁)
    (hr₀ : IsRecurrent (δ + (d.weight.natAbs : ℂ))
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) μ₀)
    (hs₀ : IsSymmetric ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) μ₀)
    (hh : Continuous h) (hu : Continuous u)
    (h₁ : ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ,
      blockFourierCoefficient 3 1 k h g = μ₁ k * blockFourierCoefficient 3 1 k f g)
    (h₀ : ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ,
      blockFourierCoefficient 3 0 k u g = μ₀ k * blockFourierCoefficient 3 0 k h g)
    (k : ℤ) {g : Langlands.GeneralLinear 3 ℝ} (hg : g ∈ unitaryCompact ℝ 3) :
    ∃ c₀ c₁ : ℂ, (μ₀ (((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2) ≠ 0 → c₀ ≠ 0) ∧
      (μ₁ (c.parity.val : ℤ) ≠ 0 → c₁ ≠ 0) ∧
      blockFourierCoefficient 3 1 k u g =
        (2 * (Real.pi : ℂ))⁻¹ * (2 * (Real.pi : ℂ))⁻¹ *
          (c₀ * c₁ * (landingPoly c d f D₀ D₁ k g).eval δ) := by
  have h01 : 0 + 1 < 3 := by norm_num
  have h12 : 1 + 1 < 3 := by norm_num
  have hχ1 : ∀ i : ℕ,
      realPositionCharacter [RealBlock.induced d, RealBlock.character c] i 1 = 1 :=
    RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _
  have hfPS : f ∈ principalSeries ℝ 3
      (realPositionCharacter [RealBlock.induced d, RealBlock.character c]) := hf.1.1
  have hfc : Continuous f := RealBlockJacquet.continuous_coe ⟨f, hf⟩
  have hε₁ : (c.parity.val : ℤ) = 0 ∨ (c.parity.val : ℤ) = 1 := by
    have := c.parity.isLt
    omega
  have hε₀ : ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2 = 0 ∨
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2 = 1 := by
    omega
  have hpar1 : ∀ i : ℤ, (-1 : ℂ) ^ i =
      realPositionCharacter [RealBlock.induced d, RealBlock.character c] 1 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.character c] 2 (-1) ↔
      Even (i - (c.parity.val : ℤ)) := by
    intro i
    rw [realPositionCharacter_induced_character_one, realPositionCharacter_induced_character_two,
      one_mul, ← zpow_natCast, neg_one_zpow_eq_iff]
  have hpar0 : ∀ j : ℤ, (-1 : ℂ) ^ j =
      realPositionCharacter [RealBlock.induced d, RealBlock.character c] 0 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.character c] 1 (-1) *
          (-1 : ℂ) ^ c.parity.val ↔
      Even (j - ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2) := by
    intro j
    rw [realPositionCharacter_induced_character_zero, realPositionCharacter_induced_character_one,
      mul_one, ← pow_add, ← zpow_natCast, neg_one_zpow_eq_iff, even_sub_iff_mod_two]
  have hI₀ : ∀ j ∈ Finset.Icc (-(D₀ : ℤ)) D₀,
      |j| ≤ ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2 + 2 * D₀ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [abs_le]
    constructor <;> omega
  have hI₁ : ∀ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, |i| ≤ (c.parity.val : ℤ) + 2 * D₁ := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [abs_le]
    constructor <;> omega
  have hB₁ : ∀ i j : ℤ, ¬ Even (i - (c.parity.val : ℤ)) →
      blockFourierCoefficient 3 1 k
        (blockFourierCoefficient 3 0 j (blockFourierCoefficient 3 1 i f)) g = 0 := by
    intro i j hi
    have hz : blockFourierCoefficient 3 1 i f = fun _ => 0 := by
      funext x
      exact blockFourierCoefficient_eq_zero_of_parity h12 hχ1 hfPS
        (fun e => hi ((hpar1 i).mp e)) x
    rw [hz, blockFourierCoefficient_zero_fun', blockFourierCoefficient_zero_fun]
  have hB₀ : ∀ ν : ℤ → ℂ, IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) ν →
      ∀ j : ℤ, ¬ Even (j - ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2) →
      ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, ν i * blockFourierCoefficient 3 1 k
        (blockFourierCoefficient 3 0 j (blockFourierCoefficient 3 1 i f)) g = 0 := by
    intro ν hν j hj
    have hvan : ∀ x, blockFourierCoefficient 3 0 j
        (fun y => ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, ν i * blockFourierCoefficient 3 1 i f y) x =
          0 :=
      blockFourierCoefficient_eq_zero_of_rotation_pi h01
        (F := fun y => ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, ν i * blockFourierCoefficient 3 1 i f y)
        (fun y => sum_blockFourierCoefficient_rotation_pi hχ1 hfPS D₁ ν
          ((-1 : ℂ) ^ c.parity.val) (fun i hi => hν i ((hpar1 i).mp hi)) y)
        (fun e => hj ((hpar0 j).mp e))
    have e1 : (fun x => ∑ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁,
        ν i * blockFourierCoefficient 3 0 j (blockFourierCoefficient 3 1 i f) x) =
          fun _ => 0 := by
      funext x
      rw [← blockFourierCoefficient_lincomb 0 j _ ν _
        (fun i _ => continuous_blockFourierCoefficient 1 i hfc) x]
      exact hvan x
    rw [← blockFourierCoefficient_lincomb 1 k _ ν _
      (fun i _ => continuous_blockFourierCoefficient 0 j
        (continuous_blockFourierCoefficient 1 i hfc)) g, e1, blockFourierCoefficient_zero_fun]
  have hexp := expansion h12 h01 hfc hD₁ hD₀ hh hu h₁ h₀ 1 k hg
  obtain ⟨c₀, c₁, hc₀, hc₁, hw⟩ := window_sum_eq hε₀ hε₁ hI₀ hI₁
    (fun i j => blockFourierCoefficient 3 1 k
      (blockFourierCoefficient 3 0 j (blockFourierCoefficient 3 1 i f)) g) hB₁ hB₀ hr₁ hs₁
    (isRecurrent_mod_two hr₀) (isSymmetric_mod_two hs₀)
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  rw [hexp]
  congr 1

/-- **Reduction of the landing from `[d, c]` to the special parameters.** -/
theorem inducedFirst_of_special (hS : SpecialLanding) : RealSwapLandingInducedFirstStatement := by
  intro c d δ μ₀ μ₁ f h u hr₁ hs₁ hr₀ hs₀ hf hh hu h₁ h₀ g hg k hk
  have hfc : Continuous f := RealBlockJacquet.continuous_coe ⟨f, hf⟩
  obtain ⟨D₁, hD₁⟩ := RealBlockJacquet.exists_bound 1 hfc hf.2
  have hDb : ∀ i : ℤ, ∃ D : ℕ, ∀ j : ℤ, (D : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j (blockFourierCoefficient 3 1 i f) g = 0 := fun i =>
    RealBlockJacquet.exists_bound 0 (continuous_blockFourierCoefficient 1 i hfc)
      (mem_kFiniteVectors_blockFourierCoefficient 1 i hfc hf.2)
  choose Db hDb using hDb
  have hD₀ : ∀ i ∈ Finset.Icc (-(D₁ : ℤ)) D₁, ∀ j : ℤ,
      (((Finset.Icc (-(D₁ : ℤ)) D₁).sup Db : ℕ) : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ 3,
        blockFourierCoefficient 3 0 j (blockFourierCoefficient 3 1 i f) g = 0 := by
    intro i hi j hj x hx
    have hle : ((Db i : ℕ) : ℤ) ≤ (((Finset.Icc (-(D₁ : ℤ)) D₁).sup Db : ℕ) : ℤ) := by
      exact_mod_cast Finset.le_sup hi
    exact hDb i j (lt_of_le_of_lt hle hj) x hx
  have hπ : (2 * (Real.pi : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
  have hε₀ : ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2 = 0 ∨
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) % 2 = 1 := by
    omega
  have hε₁ : (c.parity.val : ℤ) = 0 ∨ (c.parity.val : ℤ) = 1 := by
    have := c.parity.isLt
    omega
  have hQ : ∀ n : ℕ, (landingPoly c d f ((Finset.Icc (-(D₁ : ℤ)) D₁).sup Db) D₁ k g).eval
      ((n : ℂ) + 2) = 0 := by
    intro n
    obtain ⟨ν₀, ν₁, h', u', hr₁', hs₁', hν₁0, hν₁1, hr₀', hs₀', hν₀0, hν₀1, hh', hu', h₁', h₀',
      hL⟩ := hS c d f hf n
    obtain ⟨c₀, c₁, hc₀, hc₁, he⟩ := exists_eq_landingPoly c d hf hD₁ hD₀ hr₁' hs₁' hr₀' hs₀'
      hh' hu' h₁' h₀' k hg
    rw [hL g hg k hk] at he
    have hc₀' : c₀ ≠ 0 := hc₀ (by rcases hε₀ with e | e <;> rw [e] <;> assumption)
    have hc₁' : c₁ ≠ 0 := hc₁ (by rcases hε₁ with e | e <;> rw [e] <;> assumption)
    have := he.symm
    simpa [hπ, hc₀', hc₁'] using this
  obtain ⟨c₀, c₁, -, -, he⟩ := exists_eq_landingPoly c d hf hD₁ hD₀ hr₁ hs₁ hr₀ hs₀ hh hu h₁ h₀ k hg
  rw [he, eval_eq_zero_of_nat hQ δ, mul_zero, mul_zero]

end Reduction

end RealSwapLandingAlgebra

end Langlands.Archimedean
