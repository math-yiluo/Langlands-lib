import Langlands.Analysis.LocalEllipticSystemPointwise
import Langlands.Analysis.OrderedTensorL2InterpolationProof

/-! # Interior derivative bounds for a local elliptic equation -/

noncomputable section

open scoped ContDiff ENNReal Nat Topology
open MeasureTheory Metric Set Filter

set_option autoImplicit false

namespace Langlands.Analysis

variable {d r : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A function continuous on the closed ball has finite weighted seminorms: the Library's
`weightedSeminorm_lt_top`. -/
theorem ballWeightedSeminorm_lt_top_of_continuousOn_closedBall {G : E → ℝ} {x₀ : E} {R : ℝ}
    (hR : 0 ≤ R) (hG : ContinuousOn G (closedBall x₀ R)) (m : ℕ) :
    ballWeightedSeminorm G x₀ R m < ⊤ :=
  weightedSeminorm_lt_top hR hG m

private theorem ofReal_mul_ofReal_mul_eq {a b c e : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : a * b = c * e) (X : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * X) = ENNReal.ofReal c * (ENNReal.ofReal e * X) := by
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hc, h]

/-- The sum of the Leibniz constants of the cutoff at order `r`, multiplied by `d ^ r`. -/
def cutoffLeibnizConst (d r : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (r + 1),
    ENNReal.ofReal ((d : ℝ) ^ r * (r.choose i : ℝ) * ballCutoffConst i)

theorem cutoffLeibnizConst_ne_top (d r : ℕ) : cutoffLeibnizConst d r ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top

/-- The `L²` norm of the ordered `k`-th derivative tensor of a cutoff product is controlled by
the lower ordered tensors of the original function on the outer ball. -/
theorem eLpNorm_derivWordNorm_ballCutoff_smul_le {u : E → ℂ} {x₀ : E} {ρ σ : ℝ}
    (hρ : 0 ≤ ρ) (hρσ : ρ < σ) (hu : ContDiffOn ℝ ∞ u (ball x₀ σ)) (k : ℕ) :
    eLpNorm (derivWordNorm k (fun x => ballCutoff x₀ ρ σ x • u x)) 2 volume ≤
      ∑ i ∈ Finset.range (k + 1),
        ENNReal.ofReal ((d : ℝ) ^ k * (k.choose i : ℝ) * (ballCutoffConst i / (σ - ρ) ^ i)) *
          eLpNorm (derivWordNorm (k - i) u) 2 (volume.restrict (ball x₀ σ)) := by
  set F : E → ℂ := fun x => ballCutoff x₀ ρ σ x • u x with hFdef
  have hF : ContDiff ℝ ∞ F := contDiff_ballCutoff_smul hρ hρσ hu
  have hδ : 0 < σ - ρ := sub_pos.2 hρσ
  let c : ℕ → ℝ := fun i => (d : ℝ) ^ k * (k.choose i : ℝ) * (ballCutoffConst i / (σ - ρ) ^ i)
  have hc (i : ℕ) : 0 ≤ c i := by
    have := ballCutoffConst_nonneg i
    positivity
  let g : E → ℝ := fun x => ∑ i ∈ Finset.range (k + 1), c i * derivWordNorm (k - i) u x
  have hpt (x : E) : ‖derivWordNorm k F x‖ ≤ (ball x₀ σ).indicator g x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (derivWordNorm_nonneg _ _ _)]
    by_cases hx : x ∈ ball x₀ σ
    · rw [indicator_of_mem hx]
      calc
        derivWordNorm k F x ≤ (d : ℝ) ^ k * ‖iteratedFDeriv ℝ k F x‖ :=
          derivWordNorm_le_opNorm_times_card k F x
        _ ≤ (d : ℝ) ^ k * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
              (ballCutoffConst i / (σ - ρ) ^ i) * ‖iteratedFDeriv ℝ (k - i) u x‖ :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_ballCutoff_smul_le hρ hρσ hu hx k)
            (by positivity)
        _ ≤ g x := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := norm_iteratedFDeriv_le_derivWordNorm (k - i) u x
          have h2 : 0 ≤ (k.choose i : ℝ) * (ballCutoffConst i / (σ - ρ) ^ i) := by
            have := ballCutoffConst_nonneg i
            positivity
          calc
            _ = c i * ‖iteratedFDeriv ℝ (k - i) u x‖ := by simp only [c]; ring
            _ ≤ c i * derivWordNorm (k - i) u x := mul_le_mul_of_nonneg_left h1 (hc i)
    · rw [indicator_of_notMem hx]
      have hx' : x ∉ closedBall x₀ ((ρ + σ) / 2) := fun h =>
        hx (closedBall_subset_ball (by linarith) h)
      have hzero : F =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [ballCutoff_eventuallyEq_zero hρ hρσ hx'] with y hy
        simp [F, hy]
      have hD : iteratedFDeriv ℝ k F x = 0 := by
        rw [(hzero.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, iteratedFDeriv_fun_zero]
        rfl
      simp [derivWordNorm, hD]
  have hmeas : AEStronglyMeasurable (derivWordNorm k F) volume :=
    (continuousOn_univ.1 (continuousOn_derivWordNorm hF.contDiffOn isOpen_univ k))
      |>.aestronglyMeasurable
  have hsum : g = ∑ i ∈ Finset.range (k + 1), fun x => c i * derivWordNorm (k - i) u x := by
    funext x
    simp [g]
  calc
    eLpNorm (derivWordNorm k F) 2 volume ≤ eLpNorm ((ball x₀ σ).indicator g) 2 volume :=
      eLpNorm_mono_real hmeas hpt
    _ = eLpNorm g 2 (volume.restrict (ball x₀ σ)) :=
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet
    _ ≤ ∑ i ∈ Finset.range (k + 1),
          eLpNorm (fun x => c i * derivWordNorm (k - i) u x) 2 (volume.restrict (ball x₀ σ)) := by
      rw [hsum]
      exact eLpNorm_sum_le (by norm_num)
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      change eLpNorm (c i • derivWordNorm (k - i) u) 2 _ = _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hc i)]

/-- The `L²` norm of a cutoff product is bounded by the sup bound of the function. -/
theorem eLpNorm_ballCutoff_smul_le {u : E → ℂ} {x₀ : E} {ρ σ R M : ℝ}
    (hρ : 0 ≤ ρ) (hρσ : ρ < σ) (hσR : σ ≤ R) (hu : ContDiffOn ℝ ∞ u (ball x₀ σ))
    (hM : ∀ x ∈ closedBall x₀ R, ‖u x‖ ≤ M) :
    eLpNorm (fun x => ballCutoff x₀ ρ σ x • u x) 2 volume ≤
      volume (closedBall x₀ R) ^ (1 / 2 : ℝ) * ENNReal.ofReal M := by
  set F : E → ℂ := fun x => ballCutoff x₀ ρ σ x • u x with hFdef
  have hF : Continuous F := (contDiff_ballCutoff_smul hρ hρσ hu).continuous
  have hsupp : Function.support F ⊆ closedBall x₀ R := by
    intro x hx
    by_contra h
    apply hx
    have hx' : x ∉ ball x₀ ((ρ + σ) / 2) := fun h' =>
      h (ball_subset_closedBall (ball_subset_ball (by linarith) h'))
    simp [F, ballCutoff_eq_zero hρ hρσ hx']
  rw [← eLpNorm_restrict_eq_of_support_subset hF.aestronglyMeasurable hsupp]
  have h := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict (closedBall x₀ R)) (C := M)
    hF.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_closedBall).2 (ae_of_all _ fun x hx => by
      simp only [F, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ballCutoff_nonneg _ _ _ _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (ballCutoff_le_one _ _ _ _)).trans
        (hM x hx)))
  have hhalf : (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) := by norm_num
  rwa [Measure.restrict_apply_univ, hhalf] at h

/-- Cutting off in a smaller ball contracts the `L²` norm on a larger closed ball. -/
theorem eLpNorm_ballCutoff_smul_le_restrict {u : E → ℂ} {x₀ : E} {ρ σ R : ℝ}
    (hρ : 0 ≤ ρ) (hρσ : ρ < σ) (hσR : σ ≤ R) (hu : ContDiffOn ℝ ∞ u (ball x₀ σ)) :
    eLpNorm (fun x => ballCutoff x₀ ρ σ x • u x) 2 volume ≤
      eLpNorm u 2 (volume.restrict (closedBall x₀ R)) := by
  set F : E → ℂ := fun x => ballCutoff x₀ ρ σ x • u x
  have hF : Continuous F := (contDiff_ballCutoff_smul hρ hρσ hu).continuous
  have hsupp : Function.support F ⊆ closedBall x₀ R := by
    intro x hx
    by_contra h
    apply hx
    have hx' : x ∉ ball x₀ ((ρ + σ) / 2) := fun h' =>
      h (ball_subset_closedBall (ball_subset_ball (by linarith) h'))
    simp [F, ballCutoff_eq_zero hρ hρσ hx']
  rw [← eLpNorm_restrict_eq_of_support_subset hF.aestronglyMeasurable hsupp]
  apply eLpNorm_mono hF.aestronglyMeasurable
  intro x
  simp only [F, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ballCutoff_nonneg _ _ _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (ballCutoff_le_one _ _ _ _)

/-- **Scale-explicit interpolation of weighted seminorms.** On a ball of radius `R`, the
`k`-th weighted seminorm of a smooth function is bounded by `ε ^ (r - k)` times the sum of its
weighted seminorms up to order `r`, plus `ε⁻¹ ^ k` times a common bound for the cutoff products, for every `0 < ε`. -/
private theorem ballWeightedSeminorm_le_interpolation_of_cutoff_bound {u : E → ℂ} {x₀ : E} {R ε : ℝ} {B : ℝ≥0∞}
    (hR : 0 < R) (hε : 0 < ε) (hu : ContDiffOn ℝ ∞ u (ball x₀ R))
    (hB : ∀ ρ σ : ℝ, 0 ≤ ρ → ρ < σ → σ ≤ R →
      eLpNorm (fun x => ballCutoff x₀ ρ σ x • u x) 2 volume ≤ B)
    {k : ℕ} (hk : k ≤ r) :
    ballWeightedSeminorm (derivWordNorm k u) x₀ R k ≤
      ENNReal.ofReal (2 ^ k * ε ^ (r - k)) * (cutoffLeibnizConst d r *
          ∑ j ∈ Finset.range (r + 1), ballWeightedSeminorm (derivWordNorm j u) x₀ R j) +
        ENNReal.ofReal (2 ^ k * ε⁻¹ ^ k) *
          B := by
  set T := ∑ j ∈ Finset.range (r + 1), ballWeightedSeminorm (derivWordNorm j u) x₀ R j
  refine iSup₂_le fun ρ hρ => ?_
  have hρ0 : 0 ≤ ρ := (half_pos hR).le.trans hρ.1
  set σ := (ρ + R) / 2 with hσ
  set δ := σ - ρ with hδdef
  have hρσ : ρ < σ := by rw [hσ]; linarith [hρ.2]
  have hσR : σ < R := by rw [hσ]; linarith [hρ.2]
  have hδ : 0 < δ := sub_pos.2 hρσ
  have hRρ : R - ρ = 2 * δ := by rw [hδdef, hσ]; ring
  have hRσ : R - σ = δ := by rw [hδdef, hσ]; ring
  have hσmem : σ ∈ Ico (R / 2) R := ⟨by rw [hσ]; linarith [hρ.1], hσR⟩
  have hsm : ContDiffOn ℝ ∞ u (ball x₀ σ) := hu.mono (ball_subset_ball hσR.le)
  set F : E → ℂ := fun x => ballCutoff x₀ ρ σ x • u x with hFdef
  have hF : ContDiff ℝ ∞ F := contDiff_ballCutoff_smul hρ0 hρσ hsm
  have hFc : HasCompactSupport F := hasCompactSupport_ballCutoff_smul u hρ0 hρσ
  -- the cutoff product agrees with `u` on the inner ball
  have heq : ∀ x ∈ ball x₀ ρ, derivWordNorm k u x = derivWordNorm k F x := by
    intro x hx
    have h := ((ballCutoff_smul_eventuallyEq u hρ0 hρσ hx).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds
    simp only [derivWordNorm, ← hFdef] at h ⊢
    rw [h]
  have hstep1 : eLpNorm (derivWordNorm k u) 2 (volume.restrict (ball x₀ ρ)) ≤
      eLpNorm (derivWordNorm k F) 2 volume := by
    rw [eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ heq))]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  -- interpolation at the scale `ε * δ`
  have hI := orderedTensorL2Interpolation (d := d) (r := r) k hk (ε * δ) (by positivity) F hF hFc
  change eLpNorm (derivWordNorm k F) 2 volume ≤
      ENNReal.ofReal ((ε * δ) ^ (r - k)) * eLpNorm (derivWordNorm r F) 2 volume +
        ENNReal.ofReal ((ε * δ)⁻¹ ^ k) * eLpNorm F 2 volume at hI
  -- the top-order cutoff tensor
  have htop : ENNReal.ofReal (δ ^ r) * eLpNorm (derivWordNorm r F) 2 volume ≤
      cutoffLeibnizConst d r * T := by
    have hc := eLpNorm_derivWordNorm_ballCutoff_smul_le hρ0 hρσ hsm r
    calc
      _ ≤ ENNReal.ofReal (δ ^ r) * ∑ i ∈ Finset.range (r + 1),
            ENNReal.ofReal ((d : ℝ) ^ r * (r.choose i : ℝ) * (ballCutoffConst i / δ ^ i)) *
              eLpNorm (derivWordNorm (r - i) u) 2 (volume.restrict (ball x₀ σ)) :=
        mul_le_mul' le_rfl hc
      _ = ∑ i ∈ Finset.range (r + 1),
            ENNReal.ofReal ((d : ℝ) ^ r * (r.choose i : ℝ) * ballCutoffConst i) *
              (ENNReal.ofReal (δ ^ (r - i)) *
                eLpNorm (derivWordNorm (r - i) u) 2 (volume.restrict (ball x₀ σ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hir : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hci := ballCutoffConst_nonneg i
        refine ofReal_mul_ofReal_mul_eq (by positivity) (by positivity) ?_ _
        have hδi : δ ^ r = δ ^ i * δ ^ (r - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hir]
        rw [hδi]
        field_simp
      _ ≤ ∑ i ∈ Finset.range (r + 1),
            ENNReal.ofReal ((d : ℝ) ^ r * (r.choose i : ℝ) * ballCutoffConst i) * T := by
        refine Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl ?_
        have h := le_ballWeightedSeminorm (G := derivWordNorm (r - i) u) (x₀ := x₀) (r - i)
          hσmem
        rw [hRσ] at h
        refine h.trans ?_
        exact Finset.single_le_sum
          (f := fun j => ballWeightedSeminorm (derivWordNorm j u) x₀ R j)
          (fun _ _ => zero_le) (Finset.mem_range.2 (by omega))
      _ = cutoffLeibnizConst d r * T := by rw [cutoffLeibnizConst, Finset.sum_mul]
  have hlow := hB ρ σ hρ0 hρσ hσR.le
  calc
    ENNReal.ofReal ((R - ρ) ^ k) * eLpNorm (derivWordNorm k u) 2 (volume.restrict (ball x₀ ρ))
        ≤ ENNReal.ofReal ((2 * δ) ^ k) *
          (ENNReal.ofReal ((ε * δ) ^ (r - k)) * eLpNorm (derivWordNorm r F) 2 volume +
            ENNReal.ofReal ((ε * δ)⁻¹ ^ k) * eLpNorm F 2 volume) := by
      rw [hRρ]
      exact mul_le_mul' le_rfl (hstep1.trans hI)
    _ = ENNReal.ofReal (2 ^ k * ε ^ (r - k)) *
          (ENNReal.ofReal (δ ^ r) * eLpNorm (derivWordNorm r F) 2 volume) +
        ENNReal.ofReal (2 ^ k * ε⁻¹ ^ k) * eLpNorm F 2 volume := by
      rw [mul_add]
      congr 1
      · refine ofReal_mul_ofReal_mul_eq (by positivity) (by positivity) ?_ _
        have hδk : δ ^ r = δ ^ k * δ ^ (r - k) := by
          rw [← pow_add, Nat.add_sub_cancel' hk]
        rw [hδk]
        ring_nf
      · rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [← mul_pow, ← mul_pow, mul_inv, mul_comm ε⁻¹ δ⁻¹, ← mul_assoc, mul_assoc 2 δ δ⁻¹,
          mul_inv_cancel₀ hδ.ne', mul_one]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl htop) (mul_le_mul' le_rfl hlow)

/-- **Scale-explicit interpolation of weighted seminorms.** On a ball of radius `R`, the
`k`-th weighted seminorm of a smooth function is bounded by `ε ^ (r - k)` times the sum of its
weighted seminorms up to order `r`, plus `ε⁻¹ ^ k` times its sup bound, for every `0 < ε`. -/
theorem ballWeightedSeminorm_le_interpolation {u : E → ℂ} {x₀ : E} {R M ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hu : ContDiffOn ℝ ∞ u (ball x₀ R))
    (hM : ∀ x ∈ closedBall x₀ R, ‖u x‖ ≤ M) {k : ℕ} (hk : k ≤ r) :
    ballWeightedSeminorm (derivWordNorm k u) x₀ R k ≤
      ENNReal.ofReal (2 ^ k * ε ^ (r - k)) * (cutoffLeibnizConst d r *
          ∑ j ∈ Finset.range (r + 1), ballWeightedSeminorm (derivWordNorm j u) x₀ R j) +
        ENNReal.ofReal (2 ^ k * ε⁻¹ ^ k) *
          (volume (closedBall x₀ R) ^ (1 / 2 : ℝ) * ENNReal.ofReal M) :=
  ballWeightedSeminorm_le_interpolation_of_cutoff_bound hR hε hu
    (fun _ _ hρ hρσ hσR => eLpNorm_ballCutoff_smul_le hρ hρσ hσR
      (hu.mono (ball_subset_ball hσR)) hM) hk

/-- **Local `L²` interior estimate for a scalar elliptic equation.** If a scalar
operator of positive order `r` with smooth coefficients on an open set `S` is elliptic at
`x₀ ∈ S`, then there is a closed ball around `x₀` in `S` such that, for every order `m`, the
`m`-th derivative at `x₀` of every smooth solution of `D u = 0` on `S` is bounded by a constant
`C m` (independent of the solution) times the `L²` norm of `u` on the ball. -/
theorem exists_localElliptic_interior_derivative_l2_bounds (hr : 0 < r)
    (D : CoordinateScalarOperator E d r)
    (hD : D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) {S : Set E} (hS : IsOpen S)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d), ContDiffOn ℝ ∞ (D.coefficient k w) S)
    {x₀ : E} (hx₀ : x₀ ∈ S) (hell : ∀ ξ : E →L[ℝ] ℝ, ξ ≠ 0 → D.principalSymbol x₀ ξ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ closedBall x₀ R ⊆ S ∧
      ∃ C : ℕ → ℝ≥0∞, (∀ m, C m ≠ ⊤) ∧
        ∀ u : E → ℂ, ContDiffOn ℝ ∞ u S → (∀ x ∈ S, D.action u x = 0) →
          ∀ m, ‖iteratedFDeriv ℝ m u x₀‖ₑ ≤ C m *
            eLpNorm u 2 (volume.restrict (closedBall x₀ R)) := by
  classical
  obtain ⟨U, hUo, hxU, hUell⟩ := coordinateScalarLocalEllipticity hr D x₀
    (fun w => (hcoef (Fin.last r) w).continuousOn.continuousAt (hS.mem_nhds hx₀)) hell
  have hS' : IsOpen (S ∩ U) := hS.inter hUo
  obtain ⟨R, hR, hsub, C, hC, hbound⟩ :=
    exists_localEllipticSystem_weighted_bounds (ι := Unit) hr D hD (fun _ _ => 0) hS'
      (fun k w => (hcoef k w).mono inter_subset_left)
      (hUell.isEllipticOn.mono inter_subset_right) ⟨hx₀, hxU⟩
  have hsubS : closedBall x₀ R ⊆ S := hsub.trans inter_subset_left
  let Λ := cutoffLeibnizConst d r
  let A : ℝ≥0∞ := (r : ℝ≥0∞) * ENNReal.ofReal (2 ^ r) * Λ * (1 + C r)
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.natCast_ne_top r) ENNReal.ofReal_ne_top) (cutoffLeibnizConst_ne_top d r))
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hC r⟩)
  let ε : ℝ := 1 / (2 * (A.toReal + 1))
  have hAt : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    rw [div_le_one (by positivity)]
    linarith
  have hAε : A * ENNReal.ofReal ε ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_mul hAt]
    refine ENNReal.ofReal_le_ofReal ?_
    dsimp only [ε]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  let b : ℝ := 2 ^ r * ε⁻¹ ^ r
  let K0 : ℝ≥0∞ := ENNReal.ofReal 2 * ((r : ℝ≥0∞) * ENNReal.ofReal b)
  have hK0 : K0 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top r) ENNReal.ofReal_ne_top)
  -- Absorb the lower order seminorms into the local `L²` norm.
  have hweighted : ∀ u : E → ℂ, ContDiffOn ℝ ∞ u S → (∀ x ∈ S, D.action u x = 0) →
      ∀ m, ballWeightedSeminorm (derivWordNorm m u) x₀ R m ≤
        C m * (K0 * eLpNorm u 2 (volume.restrict (closedBall x₀ R))) := by
    intro u hu hsol
    let M := eLpNorm u 2 (volume.restrict (closedBall x₀ R))
    let N := fun j : ℕ => ballWeightedSeminorm (derivWordNorm j u) x₀ R j
    have hN (j : ℕ) : N j ≠ ⊤ :=
      (ballWeightedSeminorm_lt_top_of_continuousOn_closedBall hR.le
        ((continuousOn_derivWordNorm hu hS j).mono hsubS) j).ne
    let B := ∑ j ∈ Finset.range r, N j
    have hB : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun j _ => hN j
    have hsys := hbound (fun _ => u) (fun _ => hu.mono inter_subset_left)
      (fun _ x hx => by simpa using hsol x hx.1) B
      (fun _ m hm => Finset.single_le_sum (f := N) (fun _ _ => zero_le) (Finset.mem_range.2 hm))
    have hNC (m : ℕ) : N m ≤ C m * B := hsys () m
    have hT : ∑ j ∈ Finset.range (r + 1), N j ≤ (1 + C r) * B := by
      rw [Finset.sum_range_succ, add_mul, one_mul]
      exact add_le_add le_rfl (hNC r)
    have hball : ContDiffOn ℝ ∞ u (ball x₀ R) := hu.mono (ball_subset_closedBall.trans hsubS)
    have hk (k : ℕ) (hk : k ∈ Finset.range r) :
        N k ≤ ENNReal.ofReal (2 ^ r * ε) * (Λ * ((1 + C r) * B)) +
          ENNReal.ofReal b * M := by
      have hkr : k < r := Finset.mem_range.1 hk
      have hcut (ρ σ : ℝ) (hρ : 0 ≤ ρ) (hρσ : ρ < σ) (hσR : σ ≤ R) :
          eLpNorm (fun x => ballCutoff x₀ ρ σ x • u x) 2 volume ≤ M :=
        eLpNorm_ballCutoff_smul_le_restrict hρ hρσ hσR (hball.mono (ball_subset_ball hσR))
      refine (ballWeightedSeminorm_le_interpolation_of_cutoff_bound
        (r := r) hR hε hball hcut hkr.le).trans
        (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (mul_le_mul' le_rfl hT))
          (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl))
      · have h1 : (2 : ℝ) ^ k ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hkr.le
        have h2 : ε ^ (r - k) ≤ ε := by
          calc ε ^ (r - k) ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by omega)
            _ = ε := pow_one ε
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
      · have h1 : (2 : ℝ) ^ k ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hkr.le
        have h2 : ε⁻¹ ^ k ≤ ε⁻¹ ^ r :=
          pow_le_pow_right₀ (one_le_inv₀ hε |>.2 hε1) hkr.le
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hsum : B ≤ (A * ENNReal.ofReal ε) * B +
        (r : ℝ≥0∞) * (ENNReal.ofReal b * M) := by
      refine (Finset.sum_le_sum hk).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ r)]
      dsimp only [A]
      ring
    have hhalf : B ≤ ENNReal.ofReal (1 / 2 : ℝ) * B +
        (r : ℝ≥0∞) * (ENNReal.ofReal b * M) :=
      hsum.trans (add_le_add (mul_le_mul' hAε le_rfl) le_rfl)
    have hBK : B ≤ K0 * M := by
      refine (absorbs_half hB hhalf).trans (le_of_eq ?_)
      dsimp only [K0]
      ring
    intro m
    exact (hNC m).trans (mul_le_mul' le_rfl hBK)
  -- pointwise bounds from the weighted bounds
  let ρ := R / 2
  have hρ : 0 < ρ := half_pos hR
  have hρsub : ball x₀ ρ ⊆ ball x₀ R := ball_subset_ball (half_lt_self hR).le
  let L := fun m : ℕ => (ENNReal.ofReal ((R - ρ) ^ m))⁻¹ * C m * K0
  have hL (m : ℕ) : L m ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (pow_pos (sub_pos.2 (half_lt_self hR)) m)).ne')
      (hC m)) hK0
  let W := volume (ball x₀ ρ) ^ (1 / 2 : ℝ)
  have hWt : W ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  have hW0 : W ≠ 0 := (ENNReal.rpow_pos (measure_ball_pos volume x₀ hρ) measure_ball_lt_top.ne).ne'
  let n := Module.finrank ℝ E
  let P := fun m : ℕ => W⁻¹ * ((∑ j ∈ Finset.range (n + 1), ENNReal.ofReal (ρ ^ j / j !) *
    L (j + m)) + ENNReal.ofReal (ρ ^ (n + 1) / n !) * L (n + 1 + m))
  have hP (m : ℕ) : P m ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hW0)
    (ENNReal.add_ne_top.2
      ⟨ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hL _),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hL _)⟩)
  refine ⟨R, hR, hsubS, P, hP, ?_⟩
  intro u hu hsol m
  let M := eLpNorm u 2 (volume.restrict (closedBall x₀ R))
  have hball : ContDiffOn ℝ ∞ u (ball x₀ R) := hu.mono (ball_subset_closedBall.trans hsubS)
  have hLp (p : ℕ) : eLpNorm (iteratedFDeriv ℝ p u) 2 (volume.restrict (ball x₀ ρ))
      ≤ L p * M := by
    refine (eLpNorm_half_ball_le_weightedDerivative hR hball p).trans ?_
    dsimp only [L]
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul' le_rfl (hweighted u hu hsol p)
  have hSob := measure_ball_rpow_mul_enorm_iteratedFDeriv_le volume hρ
    (hball.mono hρsub) (le_refl n) m
  have hEval : W * ‖iteratedFDeriv ℝ m u x₀‖ₑ ≤
      ((∑ j ∈ Finset.range (n + 1), ENNReal.ofReal (ρ ^ j / j !) * L (j + m)) +
        ENNReal.ofReal (ρ ^ (n + 1) / n !) * L (n + 1 + m)) * M := by
    refine hSob.trans ?_
    simp only [add_mul, Finset.sum_mul, mul_assoc]
    exact add_le_add (Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hLp _))
      (mul_le_mul' le_rfl (hLp _))
  have hscaled := mul_le_mul' (le_refl W⁻¹) hEval
  rw [← mul_assoc W⁻¹ W, ENNReal.inv_mul_cancel hW0 hWt, one_mul, ← mul_assoc] at hscaled
  exact hscaled

/-- **Interior estimate for a local elliptic equation with smooth coefficients.** If a scalar
operator of positive order `r` with smooth coefficients on an open set `S` is elliptic at
`x₀ ∈ S`, then there is a closed ball around `x₀` in `S` such that, for every order `m`, the
`m`-th derivative at `x₀` of every smooth solution of `D u = 0` on `S` is bounded by a constant
`C m` (independent of the solution) times any bound of `‖u‖` on the ball. -/
theorem exists_localElliptic_interior_derivative_bounds_of_pos (hr : 0 < r)
    (D : CoordinateScalarOperator E d r)
    (hD : D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) {S : Set E} (hS : IsOpen S)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d), ContDiffOn ℝ ∞ (D.coefficient k w) S)
    {x₀ : E} (hx₀ : x₀ ∈ S) (hell : ∀ ξ : E →L[ℝ] ℝ, ξ ≠ 0 → D.principalSymbol x₀ ξ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ closedBall x₀ R ⊆ S ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
        ∀ u : E → ℂ, ContDiffOn ℝ ∞ u S → (∀ x ∈ S, D.action u x = 0) →
          ∀ M : ℝ, (∀ x ∈ closedBall x₀ R, ‖u x‖ ≤ M) →
            ∀ m, ‖iteratedFDeriv ℝ m u x₀‖ ≤ C m * M := by
  obtain ⟨R, hR, hRS, C, hC, hL2⟩ :=
    exists_localElliptic_interior_derivative_l2_bounds hr D hD hS hcoef hx₀ hell
  let V := volume (closedBall x₀ R) ^ (1 / 2 : ℝ)
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne
  refine ⟨R, hR, hRS, fun m => (C m * V).toReal, fun _ => ENNReal.toReal_nonneg, ?_⟩
  intro u hu hsol M hM m
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ (mem_closedBall_self hR.le))
  have huM : eLpNorm u 2 (volume.restrict (closedBall x₀ R)) ≤ V * ENNReal.ofReal M := by
    have h := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict (closedBall x₀ R))
      ((hu.continuousOn.mono hRS).aestronglyMeasurable measurableSet_closedBall)
      ((ae_restrict_iff' measurableSet_closedBall).2 (ae_of_all _ hM))
    have hhalf : (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) := by norm_num
    rwa [Measure.restrict_apply_univ, hhalf] at h
  have h := (hL2 u hu hsol m).trans (mul_le_mul' le_rfl huM)
  rw [← mul_assoc] at h
  have hx := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hC m) hV) ENNReal.ofReal_ne_top) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0, toReal_enorm] at hx

/-- **The order-zero case.** For an operator of order `0` (multiplication by a smooth
function), ellipticity at `x₀` in positive dimension means the multiplier does not vanish at
`x₀`, so every solution vanishes near `x₀`; in dimension `0` all derivatives of positive order
vanish. Either way the same conclusion as in the positive-order case holds. -/
theorem exists_localElliptic_interior_derivative_bounds_zero
    (D : CoordinateScalarOperator E d 0) {S : Set E} (hS : IsOpen S)
    (hcoef : ∀ (k : Fin (0 + 1)) (w : Fin k.val → Fin d), ContDiffOn ℝ ∞ (D.coefficient k w) S)
    {x₀ : E} (hx₀ : x₀ ∈ S) (hell : ∀ ξ : E →L[ℝ] ℝ, ξ ≠ 0 → D.principalSymbol x₀ ξ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ closedBall x₀ R ⊆ S ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
        ∀ u : E → ℂ, ContDiffOn ℝ ∞ u S → (∀ x ∈ S, D.action u x = 0) →
          ∀ M : ℝ, (∀ x ∈ closedBall x₀ R, ‖u x‖ ≤ M) →
            ∀ m, ‖iteratedFDeriv ℝ m u x₀‖ ≤ C m * M := by
  classical
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 hS x₀ hx₀
  have hsub : closedBall x₀ (ε / 2) ⊆ S := (closedBall_subset_ball (by linarith)).trans hεS
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨ε / 2, by positivity, hsub, fun m => if m = 0 then 1 else 0,
      fun m => by by_cases hm : m = 0 <;> simp [hm], ?_⟩
    intro u _ _ M hM m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simpa [norm_iteratedFDeriv_zero] using hM x₀ (mem_closedBall_self (by positivity))
    · have h0 : iteratedFDeriv ℝ m u x₀ = 0 := by
        ext v
        exact ContinuousMultilinearMap.map_coord_zero _ ⟨0, hm⟩ (Subsingleton.elim _ _)
      simp [h0, hm.ne']
  · let ξ : E →L[ℝ] ℝ := EuclideanSpace.proj (⟨0, hd⟩ : Fin d)
    have hξ : ξ ≠ 0 := by
      intro h
      have h1 := congrArg (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single ⟨0, hd⟩ 1)) h
      simp [ξ] at h1
    let c : E → ℂ := fun x => ∑ w : Fin 0 → Fin d, D.coefficient (Fin.last 0) w x
    have hPS (x : E) : D.principalSymbol x ξ = c x := by
      simp only [CoordinateScalarOperator.principalSymbol, Finset.univ_eq_empty,
        Finset.prod_empty, mul_one, c]
    have hAct (u : E → ℂ) (x : E) : D.action u x = c x * u x := by
      change ∑ k : Fin (0 + 1), ∑ w : Fin k.val → Fin d,
        D.coefficient k w x * iteratedFDeriv ℝ k.val u x (fun j => D.basis (w j)) = _
      rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => ?_
      congr 1
    have hc0 : c x₀ ≠ 0 := hPS x₀ ▸ hell ξ hξ
    have hc : ContinuousOn c S :=
      continuousOn_finsetSum _ fun w _ => (hcoef (Fin.last 0) w).continuousOn
    have hne : ∀ᶠ y in 𝓝 x₀, c y ≠ 0 :=
      (hc.continuousAt (hS.mem_nhds hx₀)).eventually_ne hc0
    refine ⟨ε / 2, by positivity, hsub, fun _ => 0, fun _ => le_rfl, ?_⟩
    intro u _ hsol M _ m
    have hu0 : u =ᶠ[𝓝 x₀] fun _ => (0 : ℂ) := by
      filter_upwards [hS.mem_nhds hx₀, hne] with y hyS hy
      have h := hsol y hyS
      rw [hAct] at h
      exact (mul_eq_zero.1 h).resolve_left hy
    have h0 : iteratedFDeriv ℝ m u x₀ = 0 := by
      rw [(hu0.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_fun_zero]
      rfl
    simp [h0]

/-- **Interior estimate for a local elliptic equation with smooth coefficients, any order.**
If a scalar operator of order `r` with smooth coefficients on an open set `S` is elliptic at
`x₀ ∈ S`, then there is a closed ball around `x₀` in `S` such that, for every order `m`, the
`m`-th derivative at `x₀` of every smooth solution of `D u = 0` on `S` is bounded by a constant
`C m` (independent of the solution) times any bound of `‖u‖` on the ball. -/
theorem exists_localElliptic_interior_derivative_bounds
    (D : CoordinateScalarOperator E d r)
    (hD : D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) {S : Set E} (hS : IsOpen S)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d), ContDiffOn ℝ ∞ (D.coefficient k w) S)
    {x₀ : E} (hx₀ : x₀ ∈ S) (hell : ∀ ξ : E →L[ℝ] ℝ, ξ ≠ 0 → D.principalSymbol x₀ ξ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ closedBall x₀ R ⊆ S ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
        ∀ u : E → ℂ, ContDiffOn ℝ ∞ u S → (∀ x ∈ S, D.action u x = 0) →
          ∀ M : ℝ, (∀ x ∈ closedBall x₀ R, ‖u x‖ ≤ M) →
            ∀ m, ‖iteratedFDeriv ℝ m u x₀‖ ≤ C m * M := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact exists_localElliptic_interior_derivative_bounds_zero D hS hcoef hx₀ hell
  · exact exists_localElliptic_interior_derivative_bounds_of_pos hr D hD hS hcoef hx₀ hell

end Langlands.Analysis
