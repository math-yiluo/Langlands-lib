import Langlands.Analysis.ConstantCoefficientEllipticL2EstimateProof
import Langlands.Analysis.CoordinateScalarFrozenDerivativeEstimateProof
import Langlands.Analysis.CoordinateScalarLocalEllipticityProof
import Langlands.Analysis.LocalEllipticCutoffEstimate

/-! # Local derivative bounds for a finite elliptic system with a common scalar action -/

noncomputable section

open scoped ContDiff ENNReal Topology
open Function Filter MeasureTheory Metric Set

set_option autoImplicit false

namespace Langlands.Analysis

variable {d r : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "e" => EuclideanSpace.basisFun (Fin d) ℝ

private theorem weightedSeminorm_mono {F G : E → ℝ} {x₀ : E} {R : ℝ}
    (hF : ContinuousOn F (ball x₀ R)) (h : ∀ x ∈ ball x₀ R, ‖F x‖ ≤ G x) (m : ℕ) :
    ballWeightedSeminorm F x₀ R m ≤ ballWeightedSeminorm G x₀ R m := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => le_iSup₂_of_le ρ hρ (mul_le_mul' le_rfl ?_)
  apply eLpNorm_mono_ae_real
    ((hF.mono (ball_subset_ball hρ.2.le)).aestronglyMeasurable measurableSet_ball)
  exact (ae_restrict_iff' measurableSet_ball).2
    (ae_of_all _ fun x hx => h x (ball_subset_ball hρ.2.le hx))

private theorem weightedSeminorm_add_le (F G : E → ℝ) (x₀ : E) (R : ℝ) (m : ℕ) :
    ballWeightedSeminorm (fun x => F x + G x) x₀ R m ≤
      ballWeightedSeminorm F x₀ R m + ballWeightedSeminorm G x₀ R m := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => ?_
  refine (mul_le_mul' le_rfl (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))).trans ?_
  rw [mul_add]
  exact add_le_add (le_iSup₂_of_le ρ hρ le_rfl) (le_iSup₂_of_le ρ hρ le_rfl)

private theorem weightedSeminorm_sum_le {ι : Type*} (s : Finset ι) (F : ι → E → ℝ)
    (x₀ : E) (R : ℝ) (m : ℕ) :
    ballWeightedSeminorm (fun x => ∑ i ∈ s, F i x) x₀ R m ≤
      ∑ i ∈ s, ballWeightedSeminorm (F i) x₀ R m := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => ?_
  have heq : (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, F i := by
    funext x
    simp
  rw [heq]
  refine (mul_le_mul' le_rfl (eLpNorm_sum_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => le_iSup₂_of_le ρ hρ le_rfl

private theorem weightedSeminorm_scale_le {c : ℝ} (hc : 0 ≤ c) (G : E → ℝ)
    (x₀ : E) {R : ℝ} (hR : 0 ≤ R) {n m : ℕ} (hnm : n ≤ m) :
    ballWeightedSeminorm (fun x => c * G x) x₀ R m ≤
      ENNReal.ofReal (c * R ^ (m - n)) * ballWeightedSeminorm G x₀ R n := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => ?_
  have hρ0 : 0 ≤ ρ := (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2)).trans hρ.1
  have ht : 0 ≤ R - ρ := sub_nonneg.2 hρ.2.le
  have hpow : (R - ρ) ^ m ≤ R ^ (m - n) * (R - ρ) ^ n := by
    rw [← Nat.sub_add_cancel hnm, pow_add, Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ ht (sub_le_self R hρ0) (m - n)) (pow_nonneg ht n)
  have hsmul :
      eLpNorm (fun x => c * G x) 2 (volume.restrict (ball x₀ ρ)) =
        ENNReal.ofReal c * eLpNorm G 2 (volume.restrict (ball x₀ ρ)) := by
    change eLpNorm (c • G) 2 (volume.restrict (ball x₀ ρ)) = _
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hc] using
      (eLpNorm_const_smul c G 2 (volume.restrict (ball x₀ ρ)))
  calc
    _ ≤ ENNReal.ofReal (c * R ^ (m - n)) *
        (ENNReal.ofReal ((R - ρ) ^ n) * eLpNorm G 2 (volume.restrict (ball x₀ ρ))) := by
      rw [hsmul, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg ht _),
        mul_comm ((R - ρ) ^ m) c, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [mul_assoc c]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hc)) le_rfl
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup₂_of_le ρ hρ le_rfl)

private theorem weightedSeminorm_lt_top {G : E → ℝ} {x₀ : E} {R : ℝ} (hR : 0 ≤ R)
    (hG : ContinuousOn G (closedBall x₀ R)) (m : ℕ) :
    ballWeightedSeminorm G x₀ R m < ⊤ := by
  have : IsFiniteMeasure (volume.restrict (closedBall x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn hG
  have hLp : MemLp G 2 (volume.restrict (closedBall x₀ R)) :=
    MemLp.of_bound (hG.aestronglyMeasurable measurableSet_closedBall) C
      ((ae_restrict_iff' measurableSet_closedBall).2 (ae_of_all _ hC))
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := R ^ m)) hLp.eLpNorm_lt_top)
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
  · have hρ0 : 0 ≤ ρ := (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2)).trans hρ.1
    exact pow_le_pow_left₀ (sub_nonneg.2 hρ.2.le) (sub_le_self R hρ0) m
  · exact eLpNorm_mono_measure G
      (Measure.restrict_mono ((ball_subset_ball hρ.2.le).trans ball_subset_closedBall) le_rfl)

private theorem derivWordNorm_const_mul (c : ℂ) {u : E → ℂ} {x : E} {p : ℕ}
    (hu : ContDiffAt ℝ p u x) :
    derivWordNorm p (fun y => c * u y) x = ‖c‖ * derivWordNorm p u x := by
  simp only [derivWordNorm, ← smul_eq_mul c, iteratedFDeriv_const_smul_apply' hu,
    smul_apply, norm_smul,
    mul_pow, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

private theorem derivWordNorm_add_le (p : ℕ) {u v : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ p u x) (hv : ContDiffAt ℝ p v x) :
    derivWordNorm p (fun y => u y + v y) x ≤ derivWordNorm p u x + derivWordNorm p v x := by
  simpa only [orderedDerivativeFamilyNorm_euclidean_singleton, derivWordNorm] using
    (orderedDerivativeFamilyNorm_add_le e p (fun _ : Unit => u) (fun _ : Unit => v) x
      (fun _ => hu) (fun _ => hv))

private theorem singletonTensorNorm_eq (p : ℕ) (u : E → ℂ) (x : E) :
    orderedDerivativeFamilyNorm e p (fun _ : Unit => u) x = derivWordNorm p u x :=
  orderedDerivativeFamilyNorm_euclidean_singleton d p u x

private theorem derivWordNorm_linearCombination_le {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (u : ι → E → ℂ) (p : ℕ) (x : E) (hu : ∀ i ∈ s, ContDiffAt ℝ p (u i) x) :
    derivWordNorm p (fun y => ∑ i ∈ s, c i * u i y) x ≤
      ∑ i ∈ s, ‖c i‖ * derivWordNorm p (u i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [derivWordNorm]
  | @insert i s hi ih =>
    have hui := hu i (Finset.mem_insert_self i s)
    have hus j (hj : j ∈ s) := hu j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    refine (derivWordNorm_add_le p (contDiffAt_const.mul hui) ?_).trans (add_le_add ?_ (ih hus))
    · exact ContDiffAt.sum fun j hj => contDiffAt_const.mul (hus j hj)
    · exact (derivWordNorm_const_mul (c i) hui).le

private theorem weightedSeminorm_linearCombination_le {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (u : ι → E → ℂ) {v : E → ℂ} {x₀ : E} {R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (ball x₀ R))
    (hv : ContDiffOn ℝ ∞ v (ball x₀ R)) (heq : EqOn v (fun y => ∑ i, c i * u i y) (ball x₀ R))
    {p m : ℕ} (hpm : p ≤ m) :
    ballWeightedSeminorm (derivWordNorm p v) x₀ R m ≤
      ∑ i, ENNReal.ofReal (‖c i‖ * R ^ (m - p)) *
        ballWeightedSeminorm (derivWordNorm p (u i)) x₀ R p := by
  refine (weightedSeminorm_mono (G := fun x => ∑ i, ‖c i‖ * derivWordNorm p (u i) x)
    (continuousOn_derivWordNorm hv isOpen_ball p) ?_ m).trans ?_
  · intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (derivWordNorm_nonneg _ _ _),
      derivWordNorm_congr_of_eventuallyEq
        (Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) heq) p]
    exact derivWordNorm_linearCombination_le Finset.univ c u p x
      (fun i _ => ((hu i).contDiffAt (isOpen_ball.mem_nhds hx)).of_le (by simp))
  · refine (weightedSeminorm_sum_le Finset.univ _ x₀ R m).trans (Finset.sum_le_sum fun i _ => ?_)
    exact weightedSeminorm_scale_le (norm_nonneg _) _ x₀ hR hpm

private theorem exists_frozenWeighted_bound
    (D : CoordinateScalarOperator E d r) (hD : D.basis = (e).toBasis)
    {x₀ : E} {R : ℝ} (hR : 0 ≤ R)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
      ContDiffOn ℝ ∞ (D.coefficient k w) (ball x₀ R))
    (b : ℕ → ℝ) (hb0 : ∀ j, 0 ≤ b j)
    (hb : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d)
      (j : ℕ) (x : E), x ∈ ball x₀ R → derivWordNorm j (D.coefficient k w) x ≤ b j)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hvar : ∀ x ∈ ball x₀ R, (∑ w : Fin r → Fin d,
      ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) ≤ ε)
    (p : ℕ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      ∀ (u : E → ℂ), ContDiffOn ℝ ∞ u (ball x₀ R) → ∀ (B : ℝ≥0∞),
        (∀ m < p + r, ballWeightedSeminorm (derivWordNorm m u) x₀ R m ≤ B) →
        ballWeightedSeminorm
          (derivWordNorm p (constCoeffAction (fun w => D.coefficient (Fin.last r) w x₀) u))
          x₀ R (p + r) ≤ ballWeightedSeminorm (derivWordNorm p (D.action u)) x₀ R (p + r) +
          ENNReal.ofReal ε * ballWeightedSeminorm (derivWordNorm (p + r) u) x₀ R (p + r) +
          L * B := by
  let Lt := ∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
    ENNReal.ofReal ((p.choose (j + 1) : ℝ) * b (j + 1) * R ^ (j + 1))
  let Ll := ∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
    ENNReal.ofReal ((p.choose j : ℝ) * b j * R ^ (r - k.val + j))
  refine ⟨Lt + Ll, ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩
  · exact ENNReal.sum_ne_top.2 fun w _ => ENNReal.sum_ne_top.2 fun j _ => ENNReal.ofReal_ne_top
  · exact ENNReal.sum_ne_top.2 fun k _ => ENNReal.sum_ne_top.2 fun w _ =>
      ENNReal.sum_ne_top.2 fun j _ => ENNReal.ofReal_ne_top
  intro u hu B hB
  let F := constCoeffAction (fun w => D.coefficient (Fin.last r) w x₀) u
  let T := fun x => ∑ _w : Fin r → Fin d, ∑ j ∈ Finset.range p,
    (p.choose (j + 1) : ℝ) * b (j + 1) * derivWordNorm (p - (j + 1) + r) u x
  let L := fun x => ∑ k : Fin r, ∑ _w : Fin k.val → Fin d, ∑ j ∈ Finset.range (p + 1),
    (p.choose j : ℝ) * b j * derivWordNorm (p - j + k.val) u x
  have hF : ContDiffOn ℝ ∞ F (ball x₀ R) := by
    change ContDiffOn ℝ ∞ (fun y => ∑ w : Fin r → Fin d,
      D.coefficient (Fin.last r) w x₀ • iteratedLineDeriv ℝ r u (e ∘ w) y) (ball x₀ R)
    exact ContDiffOn.sum fun w _ =>
      (contDiffOn_infty_iteratedLineDeriv hu isOpen_ball (e ∘ w)).const_smul _
  have hpt (x : E) (hx : x ∈ ball x₀ R) :
      ‖derivWordNorm p F x‖ ≤ derivWordNorm p (D.action u) x +
        ε * derivWordNorm (p + r) u x + (T x + L x) := by
    have h := coordinateScalarFrozenDerivativeEstimate d r D _ isOpen_ball hcoef u hu x₀ p x hx
    have hv : (fun i => D.basis i) = (e : Fin d → E) := by rw [hD]; rfl
    simp only [hv, singletonTensorNorm_eq, Function.comp_def] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (derivWordNorm_nonneg _ _ _)]
    refine h.trans ?_
    simp only [add_assoc]
    refine add_le_add le_rfl (add_le_add
      (mul_le_mul_of_nonneg_right (hvar x hx) (derivWordNorm_nonneg _ _ _)) ?_)
    refine add_le_add (Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun j _ => ?_)
      (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun j _ => ?_)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb (Fin.last r) w (j + 1) x hx) (by positivity))
        (derivWordNorm_nonneg _ _ _)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb k.castSucc w j x hx) (by positivity))
        (derivWordNorm_nonneg _ _ _)
  have hT : ballWeightedSeminorm T x₀ R (p + r) ≤ Lt * B := by
    refine (weightedSeminorm_sum_le Finset.univ _ x₀ R _).trans ?_
    simp only [Lt, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro w _
    refine (weightedSeminorm_sum_le (Finset.range p) _ x₀ R _).trans
      (Finset.sum_le_sum fun j hj => ?_)
    have hjp : j + 1 ≤ p := Finset.mem_range.1 hj
    have he : p + r - (p - (j + 1) + r) = j + 1 := by omega
    have hstart := weightedSeminorm_scale_le
      (mul_nonneg (Nat.cast_nonneg (p.choose (j + 1))) (hb0 (j + 1)))
      (derivWordNorm (p - (j + 1) + r) u) x₀ hR (by omega : p - (j + 1) + r ≤ p + r)
    rw [he] at hstart
    exact hstart.trans (mul_le_mul' le_rfl (hB _ (by omega)))
  have hL : ballWeightedSeminorm L x₀ R (p + r) ≤ Ll * B := by
    refine (weightedSeminorm_sum_le Finset.univ _ x₀ R _).trans ?_
    simp only [Ll, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ =>
      (weightedSeminorm_sum_le Finset.univ _ x₀ R _).trans (Finset.sum_le_sum fun w _ =>
        (weightedSeminorm_sum_le (Finset.range (p + 1)) _ x₀ R _).trans
          (Finset.sum_le_sum fun j hj => ?_))
    have hjp : j ≤ p := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
    have he : p + r - (p - j + k.val) = r - k.val + j := by omega
    have hstart := weightedSeminorm_scale_le (mul_nonneg (Nat.cast_nonneg (p.choose j)) (hb0 j))
      (derivWordNorm (p - j + k.val) u) x₀ hR (by omega : p - j + k.val ≤ p + r)
    rw [he] at hstart
    exact hstart.trans (mul_le_mul' le_rfl (hB _ (by omega)))
  refine (weightedSeminorm_mono (continuousOn_derivWordNorm hF isOpen_ball p) hpt _).trans ?_
  refine (weightedSeminorm_add_le _ _ x₀ R _).trans (add_le_add ?_ ?_)
  · refine (weightedSeminorm_add_le _ _ x₀ R _).trans (add_le_add le_rfl ?_)
    simpa only [Nat.sub_self, pow_zero, mul_one] using
      weightedSeminorm_scale_le hε (derivWordNorm (p + r) u) x₀ hR (le_refl (p + r))
  · rw [add_mul]
    exact (weightedSeminorm_add_le T L x₀ R _).trans (add_le_add hT hL)

private theorem exists_weightedRecursion
    (a : (Fin r → Fin d) → ℂ) (K : ℝ) :
    ∃ K₃ : ℝ, 0 < K₃ ∧ ∀ p : ℕ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (x₀ : E) (R : ℝ) (u : E → ℂ), ContDiffOn ℝ ∞ u (ball x₀ R) →
        ConstCoeffL2Bound a K (ball x₀ R) → ∀ B : ℝ≥0∞,
        (∀ m < r + p, ballWeightedSeminorm (derivWordNorm m u) x₀ R m ≤ B) →
        ballWeightedSeminorm (derivWordNorm (r + p) u) x₀ R (r + p) ≤
          ENNReal.ofReal K₃ * ballWeightedSeminorm
            (derivWordNorm p (constCoeffAction a u)) x₀ R (r + p) + C * B := by
  obtain ⟨K₃, hK₃, hrec⟩ := exists_factorial_weighted_recursion a K
  refine ⟨K₃, hK₃, fun p => ?_⟩
  let f := ENNReal.ofReal (p.factorial : ℝ)
  let g := ENNReal.ofReal (1 / (p.factorial : ℝ))
  let C := ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (1 / ((p - q).factorial : ℝ))
  refine ⟨f * ENNReal.ofReal K₃ * C, ?_, fun x₀ R u hu hP B hB => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.sum_ne_top.2 fun q _ => ENNReal.ofReal_ne_top)
  have hfg : f * g = 1 := by
    dsimp only [f, g]
    rw [← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel (by positivity), ENNReal.ofReal_one]
  let N := fun m => ballWeightedSeminorm (derivWordNorm m u) x₀ R m
  let W := ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u)) x₀ R (r + p)
  have hb : (∑ q ∈ Finset.Icc 1 r,
      ENNReal.ofReal (1 / ((p - q).factorial : ℝ)) * N (r + p - q)) ≤ C * B := by
    simp only [C, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => mul_le_mul' le_rfl (hB _ ?_)
    have hqr := Finset.mem_Icc.1 hq
    omega
  have h := (hrec x₀ R u hu hP p).trans (mul_le_mul' le_rfl (add_le_add le_rfl hb))
  change g * N (r + p) ≤ ENNReal.ofReal K₃ * (g * W + C * B) at h
  have hf := mul_le_mul' (le_refl f) h
  rwa [← mul_assoc f g, hfg, one_mul, ← mul_assoc f, mul_add, ← mul_assoc _ C B,
    ← mul_assoc (f * ENNReal.ofReal K₃) g W, mul_right_comm f _ g, hfg, one_mul] at hf

private theorem absorbs_half {X Y : ℝ≥0∞} (hX : X ≠ ⊤)
    (h : X ≤ ENNReal.ofReal (1 / 2 : ℝ) * X + Y) :
    X ≤ ENNReal.ofReal (2 : ℝ) * Y := by
  by_cases hY : Y = ⊤
  · simp [hY]
  have hh := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX, hY⟩) h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX) hY,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at hh
  apply (ENNReal.toReal_le_toReal hX (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY)).1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  linarith

private theorem exists_derivWordNorm_coefficient_bound
    (D : CoordinateScalarOperator E d r) {S : Set E} (hS : IsOpen S)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
      ContDiffOn ℝ ∞ (D.coefficient k w) S)
    {x₀ : E} {R : ℝ} (hsub : closedBall x₀ R ⊆ S) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧
      ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d) (j : ℕ) (x : E), x ∈ ball x₀ R →
        derivWordNorm j (D.coefficient k w) x ≤ b j := by
  have hb (k : Fin (r + 1)) (w : Fin k.val → Fin d) (j : ℕ) :
      ∃ B, ∀ x ∈ closedBall x₀ R, ‖derivWordNorm j (D.coefficient k w) x‖ ≤ B :=
    (isCompact_closedBall x₀ R).exists_bound_of_continuousOn
      ((continuousOn_derivWordNorm (hcoef k w) hS j).mono hsub)
  choose B hB using hb
  refine ⟨fun j => ∑ k : Fin (r + 1), ∑ w : Fin k.val → Fin d, max 0 (B k w j), ?_, ?_⟩
  · exact fun j => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun w _ => le_max_left _ _
  intro k w j x hx
  have hnorm := hB k w j x (ball_subset_closedBall hx)
  rw [Real.norm_eq_abs, abs_of_nonneg (derivWordNorm_nonneg _ _ _)] at hnorm
  refine hnorm.trans ((le_max_right 0 (B k w j)).trans ?_)
  apply (Finset.single_le_sum (f := fun w : Fin k.val → Fin d => max 0 (B k w j))
    (fun w _ => le_max_left _ _) (Finset.mem_univ w)).trans
  exact Finset.single_le_sum (f := fun k : Fin (r + 1) => ∑ w, max 0 (B k w j))
    (fun k _ => Finset.sum_nonneg fun w _ => le_max_left _ _) (Finset.mem_univ k)

/-- On a fixed sufficiently small ball, the weighted derivative seminorms of
all solutions of a fixed finite system are bounded by a common multiple of
the initial seminorms. The constants depend on the system and derivative order. -/
theorem exists_localEllipticSystem_weighted_bounds {ι : Type*} [Fintype ι] (hr : 0 < r)
    (D : CoordinateScalarOperator E d r) (hD : D.basis = (e).toBasis)
    (A : ι → ι → ℂ) {S : Set E} (hS : IsOpen S)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d), ContDiffOn ℝ ∞ (D.coefficient k w) S)
    (hell : D.IsEllipticOn S) {x₀ : E} (hx₀ : x₀ ∈ S) :
    ∃ R : ℝ, 0 < R ∧ closedBall x₀ R ⊆ S ∧
      ∃ C : ℕ → ℝ≥0∞, (∀ m, C m ≠ ⊤) ∧
        ∀ (u : ι → E → ℂ), (∀ i, ContDiffOn ℝ ∞ (u i) S) →
          (∀ i x, x ∈ S → D.action (u i) x = ∑ j, A i j * u j x) →
          ∀ B : ℝ≥0∞,
            (∀ i m, m < r → ballWeightedSeminorm (derivWordNorm m (u i)) x₀ R m ≤ B) →
              ∀ i m, ballWeightedSeminorm (derivWordNorm m (u i)) x₀ R m ≤ C m * B := by
  classical
  let a := fun w : Fin r → Fin d => D.coefficient (Fin.last r) w x₀
  have hcont (k : Fin (r + 1)) (w : Fin k.val → Fin d) :
      ContinuousAt (D.coefficient k w) x₀ :=
    (hcoef k w).continuousOn.continuousAt (hS.mem_nhds hx₀)
  obtain ⟨U, _, hxU, c, hc, hsymbol⟩ :=
    coordinateScalarLocalEllipticity hr D x₀ (hcont (Fin.last r)) (hell x₀ hx₀)
  have hfreq (ξ : E) : c * ‖ξ‖ ^ r ≤ ‖∑ w : Fin r → Fin d,
      a w * ∏ j : Fin r, (ξ (w j) : ℂ)‖ := by
    simpa only [innerSL_apply_norm, CoordinateScalarOperator.principalSymbol, hD,
      OrthonormalBasis.coe_toBasis, coe_innerSL_apply, EuclideanSpace.inner_basisFun_real, a]
      using hsymbol x₀ hxU (innerSL ℝ ξ)
  obtain ⟨K₃, hK₃, hrec⟩ := exists_weightedRecursion a c⁻¹
  let ε : ℝ := 1 / (2 * K₃)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hvarContinuous :
      ContinuousAt (fun x => ∑ w : Fin r → Fin d,
        ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) x₀ :=
    tendsto_finsetSum _ fun w _ => (continuousAt_const.sub (hcont (Fin.last r) w)).norm
  have hvarNear : ∀ᶠ x in 𝓝 x₀,
      (∑ w : Fin r → Fin d, ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) <
        ε := hvarContinuous.eventually (p := fun y : ℝ => y < ε)
    (gt_mem_nhds (by simpa using hε))
  have hNear : ∀ᶠ x in 𝓝 x₀, x ∈ S := hS.mem_nhds hx₀
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff_ball.1 (hNear.and hvarNear)
  let R := δ / 2
  have hR : 0 < R := half_pos hδ
  have hclosed : closedBall x₀ R ⊆ S :=
    fun x hx => (hδsub x (closedBall_subset_ball (half_lt_self hδ) hx)).1
  have hball : ball x₀ R ⊆ S := ball_subset_closedBall.trans hclosed
  have hvar x (hx : x ∈ ball x₀ R) := (hδsub x (ball_subset_ball (half_lt_self hδ).le hx)).2.le
  have hP : ConstCoeffL2Bound a c⁻¹ (ball x₀ R) :=
    constCoeffL2Bound_of_statement constantCoefficientEllipticL2Estimate hc hfreq _
  obtain ⟨b, hb0, hb⟩ := exists_derivWordNorm_coefficient_bound D hS hcoef hclosed
  choose L hL hfreeze using fun p => exists_frozenWeighted_bound D hD hR.le
    (fun k w => (hcoef k w).mono hball) b hb0 hb hε.le hvar p
  choose J hJ hcut using hrec
  let N := fun (u : ι → E → ℂ) (i : ι) (m : ℕ) =>
    ballWeightedSeminorm (derivWordNorm m (u i)) x₀ R m
  let T := ∑ i, ∑ j, ENNReal.ofReal (‖A i j‖ * R ^ r)
  have hT : T ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.ofReal_ne_top
  let step := fun p => ENNReal.ofReal (2 : ℝ) * (ENNReal.ofReal K₃ * (T + L p) + J p)
  have hstep p : step p ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hT, hL p⟩), hJ p⟩)
  have hstep_le (u : ι → E → ℂ) (hu : ∀ i, ContDiffOn ℝ ∞ (u i) S)
      (heq : ∀ i x, x ∈ S → D.action (u i) x = ∑ j, A i j * u j x)
      (p : ℕ) (B : ℝ≥0∞) (hB : ∀ i m, m < r + p → N u i m ≤ B) (i : ι) :
      N u i (r + p) ≤ step p * B := by
    have hsm j := (hu j).mono hball
    have hN : N u i (r + p) ≠ ⊤ :=
      (weightedSeminorm_lt_top hR.le ((continuousOn_derivWordNorm (hu i) hS _).mono hclosed) _).ne
    have hAction : ContDiffOn ℝ ∞ (D.action (u i)) (ball x₀ R) :=
      (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hsm j)).congr fun x hx => heq i x (hball hx)
    have hforcing : ballWeightedSeminorm (derivWordNorm p (D.action (u i))) x₀ R (p + r)
        ≤ T * B := by
      refine (weightedSeminorm_linearCombination_le (A i) u hR.le hsm hAction
        (fun x hx => heq i x (hball hx)) (by omega : p ≤ p + r)).trans ?_
      rw [Nat.add_sub_cancel_left]
      refine (Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hB j p (by omega))).trans ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul' (Finset.single_le_sum
        (f := fun i => ∑ j, ENNReal.ofReal (‖A i j‖ * R ^ r))
        (fun _ _ => zero_le) (Finset.mem_univ i)) le_rfl
    have hF := (hfreeze p (u i) (hsm i) B (fun m hm => hB i m (by omega))).trans
      (add_le_add (add_le_add hforcing le_rfl) le_rfl)
    rw [Nat.add_comm p r] at hF
    have hεK : ENNReal.ofReal K₃ * ENNReal.ofReal ε = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_mul hK₃.le]
      congr 1
      dsimp [ε]
      field_simp
    dsimp only [step]
    rw [mul_assoc]
    refine absorbs_half hN ?_
    calc
      _ ≤ ENNReal.ofReal K₃ * ((T * B + ENNReal.ofReal ε * N u i (r + p)) + L p * B) +
          J p * B :=
        (hcut p x₀ R (u i) (hsm i) hP B (hB i)).trans (add_le_add (mul_le_mul' le_rfl hF) le_rfl)
      _ = (ENNReal.ofReal K₃ * ENNReal.ofReal ε) * N u i (r + p) +
          (ENNReal.ofReal K₃ * (T + L p) + J p) * B := by
        simp only [add_mul, mul_add, mul_assoc]
        simp only [add_comm, add_left_comm, mul_comm, mul_left_comm]
      _ = _ := by rw [hεK]
  have horder (m : ℕ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (u : ι → E → ℂ), (∀ i, ContDiffOn ℝ ∞ (u i) S) →
        (∀ i x, x ∈ S → D.action (u i) x = ∑ j, A i j * u j x) →
        ∀ B : ℝ≥0∞, (∀ i k, k < r → N u i k ≤ B) → ∀ i, N u i m ≤ C * B := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm : m < r
      · exact ⟨1, ENNReal.one_ne_top, fun u _ _ B hB i => by simpa only [one_mul] using hB i m hm⟩
      let p := m - r
      have hmp : r + p = m := Nat.add_sub_of_le (Nat.le_of_not_gt hm)
      choose C hC hbound using fun k : Fin m => ih k.val k.isLt
      refine ⟨step p * ∑ k, C k, ENNReal.mul_ne_top (hstep p)
        (ENNReal.sum_ne_top.2 fun k _ => hC k), fun u hu heq B hB i => ?_⟩
      rw [mul_assoc, ← show N u i (r + p) = N u i m from congrArg (N u i) hmp]
      refine hstep_le u hu heq p _ ?_ i
      intro j k hk
      let l : Fin m := ⟨k, hk.trans_eq hmp⟩
      exact (hbound l u hu heq B hB j).trans
        (mul_le_mul' (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ l)) le_rfl)
  choose C hC hbound using horder
  exact ⟨R, hR, hclosed, C, hC, fun u hu heq B hB i m => hbound m u hu heq B hB i⟩

end Langlands.Analysis
