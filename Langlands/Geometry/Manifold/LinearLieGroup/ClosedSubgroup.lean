import Langlands.Geometry.Manifold.LinearLieGroup.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The closed-subgroup theorem for linear groups

Let `𝔸` be a complete normed real algebra.

* `tendsto_exp_mul_exp_pow`: the Lie–Trotter product formula
  `(exp (X / n) exp (Y / n))^n → exp (X + Y)`.
* `lieAlgebra G = {X | ∀ t : ℝ, exp (t X) ∈ G}` for a subgroup `G` of `𝔸ˣ`, and
  `IsExpLieAlgebra.coe_eq_lieAlgebra`: if `IsExpLieAlgebra G 𝔤` then `𝔤 = lieAlgebra G`, so the
  Lie algebra in the structure is determined by `G`.
* For `𝔸` finite-dimensional and `G` closed, `lieSubmodule G hG` is `lieAlgebra G` as a subspace
  (closed under addition by Lie–Trotter), and `isExpLieAlgebra_of_isClosed`:
  `IsExpLieAlgebra G (lieSubmodule G hG)` (von Neumann's closed-subgroup theorem).

With `IsExpLieAlgebra.isClosed` (`Basic`) this shows that a subgroup of `𝔸ˣ` carries the structure
`IsExpLieAlgebra` for some `𝔤` exactly when it is closed, and that `𝔤` is then `lieAlgebra G`.

The steps of the proof are in the namespace `Langlands.LinearLieGroup.ClosedSubgroup`; they are
stated for closed multiplicative subsets `S ∋ 1` of `𝔸` (here the closure of the image of `G`).
-/

noncomputable section

open Filter Topology

namespace Langlands.LinearLieGroup

namespace ClosedSubgroup

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- `‖x^n u‖ ≤ ‖x‖^n ‖u‖`. -/
theorem norm_pow_mul_le (x u : 𝔸) (n : ℕ) : ‖x ^ n * u‖ ≤ ‖x‖ ^ n * ‖u‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

/-- `‖exp x · u‖ ≤ e^{‖x‖} ‖u‖`, from the exponential series. -/
theorem norm_exp_mul_le (x u : 𝔸) : ‖NormedSpace.exp x * u‖ ≤ Real.exp ‖x‖ * ‖u‖ := by
  have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • x ^ n) * u) (NormedSpace.exp x * u) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_right u
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n) * ‖u‖) (Real.exp ‖x‖ * ‖u‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖).mul_right ‖u‖
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [smul_mul_assoc, norm_smul, smul_eq_mul, mul_assoc, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_mul_le x u n) (by positivity)

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- If left multiplication by `a` has norm at most `q ≥ 0`, then left multiplication by `a^m` has norm at
most `q^m`. -/
theorem norm_pow_mul_le' {a : 𝔸} {q : ℝ} (hq : 0 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖) (m : ℕ)
    (u : 𝔸) :
    ‖a ^ m * u‖ ≤ q ^ m * ‖u‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (ha _).trans (mul_le_mul_of_nonneg_left ih hq)

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- `‖a^m - b^m‖ ≤ m q^m ‖a - b‖ ‖1‖` when left multiplication by `a` and by `b` have norm at most
`q ≥ 1` (telescoping). -/
theorem norm_pow_sub_pow_le {a b : 𝔸} {q : ℝ} (hq : 1 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖)
    (hb : ∀ u, ‖b * u‖ ≤ q * ‖u‖) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ (m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      rw [pow_succ', pow_succ']; noncomm_ring
    have h1 : ‖a * (a ^ m - b ^ m)‖ ≤ q * ((m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖)) :=
      (ha _).trans (mul_le_mul_of_nonneg_left ih hq0)
    have h2 : ‖b ^ m‖ ≤ q ^ (m + 1) * ‖(1 : 𝔸)‖ := by
      have := norm_pow_mul_le' hq0 hb m 1
      rw [mul_one] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact pow_le_pow_right₀ hq (Nat.le_succ m)
    have h3 : ‖(a - b) * b ^ m‖ ≤ ‖a - b‖ * (q ^ (m + 1) * ‖(1 : 𝔸)‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 h3).trans (le_of_eq ?_))
    push_cast
    ring

/-- `t ↦ exp (t X) exp (t Y) - exp (t (X + Y))` has derivative `0` at `0`. -/
theorem diff_hasDerivAt (X Y : 𝔸) :
    HasDerivAt
        (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) -
          NormedSpace.exp (t • (X + Y))) 0 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
  have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X + Y) 0
  have h := (h1.mul h2).sub h3
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, sub_self] at h
  exact h

/-- The Lie–Trotter product formula (internal form of `tendsto_exp_mul_exp_pow`). -/
theorem trotter (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set s : ℝ := ‖X‖ + ‖Y‖ with hs
  have hs0 : 0 ≤ s := by positivity
  set F : ℝ → 𝔸 := fun t : ℝ =>
    NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) - NormedSpace.exp (t • (X + Y)) with hF
  have hF0 : F 0 = 0 := by simp [hF, NormedSpace.exp_zero]
  have hsl := (diff_hasDerivAt X Y).tendsto_slope_zero
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact (inv_pos.2 this).ne'
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) • F ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    have := hsl.comp hinv
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, inv_inv]
    rw [show NormedSpace.exp ((0 : ℝ) • X) * NormedSpace.exp ((0 : ℝ) • Y) -
        NormedSpace.exp ((0 : ℝ) • (X + Y)) = 0 from hF0, sub_zero]
  have h2 : Tendsto (fun n : ℕ => Real.exp s * ‖(1 : 𝔸)‖ * ‖(n : ℝ) • F ((n : ℝ)⁻¹)‖) atTop
      (𝓝 0) := by
    have := (h1.norm).const_mul (Real.exp s * ‖(1 : 𝔸)‖)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h2
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hni : (0 : ℝ) ≤ (n : ℝ)⁻¹ := (inv_pos.2 hn0).le
  have hb : NormedSpace.exp (X + Y) = NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) ^ n := by
    rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  have hq : (1 : ℝ) ≤ Real.exp ((n : ℝ)⁻¹ * s) := Real.one_le_exp (by positivity)
  have ha : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y) * u‖ ≤
      Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    rw [mul_assoc]
    refine (norm_exp_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (norm_exp_mul_le _ _) (Real.exp_pos _).le).trans (le_of_eq ?_)
    rw [← mul_assoc, ← Real.exp_add, norm_smul, norm_smul, Real.norm_of_nonneg hni, hs, mul_add]
  have hb' : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) * u‖ ≤
      Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    refine (norm_exp_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [Real.exp_le_exp, norm_smul, Real.norm_of_nonneg hni]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hni
  rw [hb]
  refine (norm_pow_sub_pow_le hq ha hb' n).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, show (n : ℝ) * ((n : ℝ)⁻¹ * s) = s by field_simp, norm_smul,
    Real.norm_of_nonneg hn0.le]
  ring
omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- A multiplicative set containing `1` contains the powers of its elements. -/
theorem pow_mem_of_mul {S : Set 𝔸} (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {a : 𝔸}
    (ha : a ∈ S) (n : ℕ) :
    a ^ n ∈ S := by
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ]; exact hm _ ih _ ha

/-- The subspace `{X | ∀ t, exp (t X) ∈ S}` of a closed multiplicative subset `S ∋ 1` of `𝔸`: it is
closed under addition by the Lie–Trotter formula, `exp (t (X + Y)) = lim (exp (t X / n) exp (t Y / n))^n`. -/
def lieSub (S : Set 𝔸) (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) :
    Submodule ℝ 𝔸 where
  carrier := {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ S}
  zero_mem' := by intro t; simpa [NormedSpace.exp_zero] using h1
  add_mem' := by
    intro X Y hX hY t
    rw [smul_add]
    refine hc.mem_of_tendsto (trotter (t • X) (t • Y)) (Eventually.of_forall fun n => ?_)
    refine pow_mem_of_mul h1 hm (hm _ ?_ _ ?_) n
    · rw [smul_smul]; exact hX _
    · rw [smul_smul]; exact hY _
  smul_mem' := by
    intro c X hX t
    rw [smul_smul]; exact hX _

/-- If `y n → 0`, `y n ≠ 0`, `exp (y n) ∈ S` and `y n / ‖y n‖ → u`, then `exp (t u) ∈ S` for all `t`:
`t u` is the limit of the integer multiples `⌊t / ‖y n‖⌋ y n`. -/
theorem exp_smul_mem_of_tendsto {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) {y : ℕ → 𝔸} {u : 𝔸}
    (hy0 : Tendsto y atTop (𝓝 0)) (hne : ∀ n, y n ≠ 0) (hS : ∀ n, NormedSpace.exp (y n) ∈ S)
    (hu : Tendsto (fun n => ‖y n‖⁻¹ • y n) atTop (𝓝 u)) (t : ℝ) : NormedSpace.exp (t • u) ∈ S := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have key : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • u) ∈ S := by
    intro t ht
    have hpos : ∀ n, 0 < ‖y n‖ := fun n => norm_pos_iff.2 (hne n)
    have hn0 : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by simpa using hy0.norm
    have hk : Tendsto (fun n => ((⌊t / ‖y n‖⌋₊ : ℕ) : ℝ) * ‖y n‖) atTop (𝓝 t) := by
      have hl : Tendsto (fun n => t - ‖y n‖) atTop (𝓝 t) := by simpa using hn0.const_sub t
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun n => ?_)
          (fun n => ?_)
      · have h := (Nat.lt_floor_add_one (t / ‖y n‖)).le
        rw [div_le_iff₀ (hpos n)] at h
        show t - ‖y n‖ ≤ _
        nlinarith
      · have h := Nat.floor_le (div_nonneg ht (hpos n).le)
        rw [le_div_iff₀ (hpos n)] at h
        exact h
    have hlim := (NormedSpace.exp_continuous.tendsto _).comp (hk.smul hu)
    refine hc.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have e : (((⌊t / ‖y n‖⌋₊ : ℕ) : ℝ) * ‖y n‖) • ‖y n‖⁻¹ • y n = (⌊t / ‖y n‖⌋₊ : ℕ) • y n := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hpos n).ne', mul_one, Nat.cast_smul_eq_nsmul]
    simp only [Function.comp]
    rw [e, NormedSpace.exp_nsmul]
    exact pow_mem_of_mul h1 hm (hS n) _
  rcases le_total 0 t with ht | ht
  · exact key t ht
  · have := hi _ (key (-t) (by linarith))
    rwa [neg_smul, neg_neg] at this

/-- For a complement `W` of the Lie algebra, near `0` the only `y ∈ W` with `exp y ∈ S` is `0`
(otherwise normalized such `y` accumulate at a unit vector of the Lie algebra lying in `W`). -/
theorem eventually_eq_zero [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
        (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S)
    {W : Submodule ℝ 𝔸} (hW : Disjoint (lieSub S hc h1 hm) W) :
    ∀ᶠ y in 𝓝 (0 : 𝔸), y ∈ W → NormedSpace.exp y ∈ S → y = 0 := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨y, hy0, hy⟩ := exists_seq_forall_of_frequently hcon
  push Not at hy
  have : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  have hsph : ∀ n, ‖y n‖⁻¹ • y n ∈ Metric.sphere (0 : 𝔸) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (hy n).2.2)]
  obtain ⟨u, hu1, φ, hφ, hu⟩ := (isCompact_sphere (0 : 𝔸) 1).tendsto_subseq hsph
  have huL : u ∈ lieSub S hc h1 hm :=
    exp_smul_mem_of_tendsto hc h1 hm hi (y := y ∘ φ) (hy0.comp hφ.tendsto_atTop)
        (fun n => (hy _).2.2)
      (fun n => (hy _).2.1) hu
  have huW : u ∈ W :=
    W.closed_of_finiteDimensional.mem_of_tendsto hu
        (Eventually.of_forall fun n => W.smul_mem _ (hy _).1)
  have h0 : u = 0 := (Submodule.disjoint_def.1 hW) u huL huW
  rw [h0] at hu1
  simp at hu1

/-- For a continuous linear projection `p`, `z ↦ exp (p z) exp (z - p z)` maps neighbourhoods of `0` onto
neighbourhoods of `1` (its derivative at `0` is the identity). -/
theorem map_exp_mul_exp (p : 𝔸 →L[ℝ] 𝔸) :
    map (fun z => NormedSpace.exp (p z) * NormedSpace.exp (z - p z)) (𝓝 0) = 𝓝 (1 : 𝔸) := by
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) :=
      hasStrictFDerivAt_exp_zero
  have h1 : HasStrictFDerivAt (fun z => NormedSpace.exp (p z)) ((1 : 𝔸 →L[ℝ] 𝔸).comp p) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (by rw [map_zero]; exact hexp) p.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have h3 := h1.mul' h2
  have h4 : HasStrictFDerivAt (fun z => NormedSpace.exp (p z) * NormedSpace.exp (z - p z))
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine h3.congr_fderiv ?_
    ext z
    simp [NormedSpace.exp_zero]
  have h5 := h4.map_nhds_eq_of_equiv
  simpa [NormedSpace.exp_zero] using h5

/-- **von Neumann's argument.** Near `1`, every element of a closed multiplicative subset `S ∋ 1` of a
finite-dimensional algebra which is closed under `exp Z ↦ exp (-Z)` is `exp X` for some `X` of a
prescribed neighbourhood of `0` with `exp (t X) ∈ S` for all `t`. -/
theorem eventually_exists_exp [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S)
    (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
        (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S)
    {U : Set 𝔸} (hU : U ∈ 𝓝 (0 : 𝔸)) :
    ∀ᶠ g in 𝓝 (1 : 𝔸), g ∈ S →
      ∃ X ∈ U, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ S) ∧ NormedSpace.exp X = g := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap ((lieSub S hc h1 hm).projection W hW)
  have hpL : ∀ z, p z ∈ lieSub S hc h1 hm := fun z => Submodule.projection_apply_mem hW z
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  rw [← map_exp_mul_exp p, eventually_map]
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  filter_upwards [hp0.eventually hU, hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint)]
      with z hz1 hz2 hg
  have hneg : NormedSpace.exp (-p z) ∈ S := by simpa using hpL z (-1)
  have hq : NormedSpace.exp (z - p z) ∈ S := by
    have h := hm _ hneg _ hg
    rwa [← mul_assoc, ← NormedSpace.exp_add_of_commute (Commute.refl (p z)).neg_left, neg_add_cancel,
      NormedSpace.exp_zero, one_mul] at h
  refine ⟨p z, hz1, hpL z, ?_⟩
  rw [hz2 (hqW z) hq, NormedSpace.exp_zero, mul_one]

end ClosedSubgroup

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The Lie–Trotter product formula** in a complete normed real algebra:
`(exp (X / n) exp (Y / n))^n → exp (X + Y)`. -/
theorem tendsto_exp_mul_exp_pow (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y)) ^ n) atTop
      (𝓝 (exp (X + Y))) :=
  ClosedSubgroup.trotter X Y

/-- The Lie algebra of a subgroup `G` of `𝔸ˣ`, as a set: the `X` with `exp (t X) ∈ G` for all real `t`. -/
def lieAlgebra (G : Subgroup 𝔸ˣ) : Set 𝔸 := {X | ∀ t : ℝ, expUnit 𝔸 (t • X) ∈ G}

/-- **`𝔤` is determined by `G`.** If `IsExpLieAlgebra G 𝔤`, then `𝔤` is the set of `X` with
`exp (t X) ∈ G` for all `t`: one inclusion is `expUnit_mem`, the other follows from `exists_nhds`
applied to `t X` for small `t ≠ 0`. -/
theorem IsExpLieAlgebra.coe_eq_lieAlgebra {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
    (h : IsExpLieAlgebra G 𝔤) : (𝔤 : Set 𝔸) = lieAlgebra G := by
  ext X
  refine ⟨fun hX t => h.expUnit_mem _ (𝔤.smul_mem t hX), fun hX => ?_⟩
  obtain ⟨U, hUo, hU0, -, hU⟩ := h.exists_nhds
  have hc : Continuous fun t : ℝ => t • X := continuous_id.smul continuous_const
  have hmem : (fun t : ℝ => t • X) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hUo.mem_nhds hU0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  have ht : (ε / 2) • X ∈ U := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith)
  have h1 : (ε / 2) • X ∈ 𝔤 := hU _ ht (hX _)
  have h2 := 𝔤.smul_mem (ε / 2)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h2

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- The closure in `𝔸` of the image of `G`, as a submonoid. -/
def closureImage (G : Subgroup 𝔸ˣ) : Submonoid 𝔸 :=
  (G.toSubmonoid.map (Units.coeHom 𝔸)).topologicalClosure

omit [NormedAlgebra ℝ 𝔸] in
/-- For a closed subgroup `G` of `𝔸ˣ`, a unit lies in the closure of the image of `G` in `𝔸` only if it
lies in `G`. -/
theorem coe_mem_closureImage_iff {G : Subgroup 𝔸ˣ} (hG : IsClosed (G : Set 𝔸ˣ)) (u : 𝔸ˣ) :
    (u : 𝔸) ∈ closureImage G ↔ u ∈ G := by
  refine ⟨fun hu => ?_, fun hu => subset_closure ⟨u, hu, rfl⟩⟩
  have : u ∈ closure (G : Set 𝔸ˣ) := by
    rw [Units.isOpenEmbedding_val.isInducing.closure_eq_preimage_closure_image]
    exact hu
  rwa [hG.closure_eq] at this

/-- The Lie algebra of a closed subgroup of `𝔸ˣ` as a subspace of `𝔸`; its underlying set is
`lieAlgebra G` by definition. That it is closed under addition is the Lie–Trotter formula. -/
def lieSubmodule (G : Subgroup 𝔸ˣ) (hG : IsClosed (G : Set 𝔸ˣ)) : Submodule ℝ 𝔸 :=
  (ClosedSubgroup.lieSub (closureImage G : Set 𝔸) isClosed_closure (closureImage G).one_mem
    fun _ ha _ hb => (closureImage G).mul_mem ha hb).copy (lieAlgebra G) (by
      ext X
      exact forall_congr' fun t => (coe_mem_closureImage_iff hG (expUnit 𝔸 (t • X))).symm)

/-- The underlying set of `lieSubmodule G hG` is `lieAlgebra G`. -/
theorem coe_lieSubmodule (G : Subgroup 𝔸ˣ) (hG : IsClosed (G : Set 𝔸ˣ)) :
    (lieSubmodule G hG : Set 𝔸) = lieAlgebra G := rfl

/-- `X ∈ lieSubmodule G hG` if and only if `exp (t X) ∈ G` for all real `t`. -/
theorem mem_lieSubmodule {G : Subgroup 𝔸ˣ} (hG : IsClosed (G : Set 𝔸ˣ)) {X : 𝔸} :
    X ∈ lieSubmodule G hG ↔ ∀ t : ℝ, expUnit 𝔸 (t • X) ∈ G := Iff.rfl

section Closed

variable [FiniteDimensional ℝ 𝔸]

/-- **The closed-subgroup theorem for linear groups (von Neumann).** Every closed subgroup `G` of `𝔸ˣ`
has the exponential Lie algebra `lieSubmodule G hG`, so it is a Lie group with the exponential charts
of `Basic`. -/
theorem isExpLieAlgebra_of_isClosed (G : Subgroup 𝔸ˣ) (hG : IsClosed (G : Set 𝔸ˣ)) :
    IsExpLieAlgebra G (lieSubmodule G hG) := by
  set M := closureImage G with hM
  have hc : IsClosed (M : Set 𝔸) := isClosed_closure
  have hsub : ∀ u ∈ G, (u : 𝔸) ∈ (M : Set 𝔸) := fun u hu => (coe_mem_closureImage_iff hG u).2 hu
  have hcl : ∀ u : 𝔸ˣ, (u : 𝔸) ∈ (M : Set 𝔸) → u ∈ G := fun u hu =>
    (coe_mem_closureImage_iff hG u).1 hu
  have hm : ∀ a ∈ (M : Set 𝔸), ∀ b ∈ (M : Set 𝔸), a * b ∈ (M : Set 𝔸) := fun a ha b hb =>
    M.mul_mem ha hb
  have hi : ∀ Z : 𝔸, exp Z ∈ (M : Set 𝔸) → exp (-Z) ∈ (M : Set 𝔸) := fun Z hZ =>
    hsub _ (G.inv_mem (hcl (expUnit 𝔸 Z) hZ))
  refine ⟨fun X hX => by simpa using hX 1, ?_⟩
  have hs := (expPartialHomeomorph 𝔸).open_source.mem_nhds (zero_mem_expPartialHomeomorph_source 𝔸)
  have h1 := ClosedSubgroup.eventually_exists_exp hc M.one_mem hm hi hs
  have h2 : Tendsto (exp : 𝔸 → 𝔸) (𝓝 0) (𝓝 1) := by
    simpa using (contDiff_exp 𝔸 (n := 0)).continuous.tendsto 0
  obtain ⟨U, hU, hUo, h0⟩ := mem_nhds_iff.1 ((h2.eventually h1).and hs)
  refine ⟨U, hUo, h0, fun X hX => (hU hX).2, fun X hX hG' => ?_⟩
  obtain ⟨Y, hY, hY', e⟩ := (hU hX).1 (hsub _ hG')
  obtain rfl : Y = X := (expPartialHomeomorph 𝔸).injOn hY (hU hX).2 e
  exact fun t => hcl _ (hY' t)

end Closed

end Langlands.LinearLieGroup
