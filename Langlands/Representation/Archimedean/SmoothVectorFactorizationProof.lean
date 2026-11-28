import Langlands.Representation.Archimedean.SmoothVectorFactorizationStatement
import Langlands.Analysis.DixmierMalliavin.DirectionalSeries
import Langlands.Analysis.DixmierMalliavin.IteratedKernel
import Langlands.Analysis.DixmierMalliavin.Line
import Langlands.Geometry.Manifold.LinearLieGroup.HaarDensity
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Smooth-vector factorization for the representation of a closed linear Lie group -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace Langlands.Archimedean

open Langlands.LinearLieGroup
open Langlands.Analysis.DixmierMalliavin

universe uA uM uG uE

private theorem iteratedDeriv_compCLM {E E' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (L : E →L[ℂ] E') {F : ℝ → E} (hF : ContDiff ℝ ∞ F) (p : ℕ) (t : ℝ) :
    iteratedDeriv p (L ∘ F) t = L (iteratedDeriv p F t) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ p (L.restrictScalars ℝ ∘ F) t (fun _ => 1) = _
  rw [(L.restrictScalars ℝ).iteratedFDeriv_comp_left
    (hF.contDiffAt (x := t)) (by simp : (p : WithTop ℕ∞) ≤ ∞)]
  rfl

private theorem eq_of_dual_unitBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E} (h : ∀ L : E →L[ℂ] ℂ, ‖L‖ ≤ 1 → L u = L v) : u = v := by
  obtain ⟨L, hL, hnorm⟩ := exists_dual_vector'' ℂ (u - v)
  rw [map_sub, h L hL, sub_self] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hnorm.symm))

section ExponentialCharts

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {G : Subgroup Aˣ} {𝔤 : Submodule ℝ A}
  (h : IsExpLieAlgebra G 𝔤) {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, 𝔤)

private abbrev ExponentialSmoothVector (v : E) : Prop :=
  letI := h.chartedSpace
  IsSmoothVector I π v

local notation "Smooth" => ExponentialSmoothVector h π

private def exponentialOrbit (X : 𝔤) (v : E) : ℝ → E :=
  fun t => π (h.expG (t • X)) v

private theorem contDiff_exponentialOrbit (X : 𝔤) {v : E} (hv : Smooth v) :
    ContDiff ℝ ∞ (exponentialOrbit h π X v) := by
  let := h.chartedSpace
  exact (hv.comp (h.contMDiff_expG_comp (contDiff_id.smul contDiff_const))).contDiff

private theorem iteratedDeriv_exponentialOrbit (X : 𝔤) {v : E} (hv : Smooth v)
    (p : ℕ) (s : ℝ) :
    iteratedDeriv p (exponentialOrbit h π X v) s =
      π (h.expG (s • X)) (iteratedDeriv p (exponentialOrbit h π X v) 0) := by
  let F := exponentialOrbit h π X v
  have hshift : (fun t : ℝ => F (t + s)) = π (h.expG (s • X)) ∘ F := by
    funext t
    change π (h.expG ((t + s) • X)) v = π (h.expG (s • X)) (π (h.expG (t • X)) v)
    rw [add_comm t s, h.expG_add_smul, map_mul, mul_apply_eq_comp]
  have he := congrFun (iteratedDeriv_comp_add_const p F s) 0
  rw [hshift, iteratedDeriv_compCLM _ (contDiff_exponentialOrbit h π X hv), zero_add] at he
  exact he.symm

private theorem smoothVector_iteratedDeriv_exponentialOrbit (X : 𝔤)
    {v : E} (hv : Smooth v) (p : ℕ) :
    Smooth (iteratedDeriv p (exponentialOrbit h π X v) 0) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  change ContMDiff I 𝓘(ℝ, E) ∞
    (orbitMap π (iteratedDeriv p (exponentialOrbit h π X v) 0))
  apply (h.contMDiff_iff_expG _).2
  intro g
  let ψ : 𝔤 × ℝ → E := fun q => π (g * h.expG q.1 * h.expG (q.2 • X)) v
  have hψ : ContDiff ℝ ∞ ψ := by
    apply (hv.comp ?_).contDiff
    exact (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_fst)).mul
      (h.contMDiff_expG_comp (contDiff_snd.smul contDiff_const))
  convert contDiff_iteratedDeriv_snd p hψ 0 using 1
  funext Y
  have he : (fun t => ψ (Y, t)) = π (g * h.expG Y) ∘ exponentialOrbit h π X v := by
    funext t
    change π (g * h.expG Y * h.expG (t • X)) v = _
    rw [map_mul, mul_apply_eq_comp]
    rfl
  rw [he, iteratedDeriv_compCLM _ (contDiff_exponentialOrbit h π X hv)]
  rfl

variable [CompleteSpace E]

/-- Bounds for the line derivatives and a smooth limit of their series in one
exponential chart. Translation transports the chart calculation to every point. -/
private theorem exists_exponentialOrbit_bounds (X : 𝔤) {v : E} (hv : Smooth v)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ M : ℕ → ℝ, (∀ p, ∀ t ∈ Icc 0 ε,
      ‖iteratedDeriv p (exponentialOrbit h π X v) t‖ ≤ M p) ∧
      ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) →
        Summable (fun p => (c p : ℂ) • iteratedDeriv p (exponentialOrbit h π X v) 0) ∧
        Smooth (∑' p, (c p : ℂ) • iteratedDeriv p (exponentialOrbit h π X v) 0) := by
  let F := exponentialOrbit h π X v
  let u : ℕ → E := fun p => iteratedDeriv p F 0
  let β : ContDiffBump (0 : 𝔤) := ⟨1, 2, one_pos, one_lt_two⟩
  let Φ : ℕ → 𝔤 → E := fun p Y => β Y • π (h.expG Y) (u p)
  let := h.chartedSpace
  have hΦ (p : ℕ) : ContDiff ℝ ∞ (Φ p) :=
    β.contDiff.smul (((smoothVector_iteratedDeriv_exponentialOrbit h π X hv p).comp
      h.contMDiff_expG).contDiff)
  have hΦc (p : ℕ) : HasCompactSupport (Φ p) := β.hasCompactSupport.smul_right
  have hBounds (p k : ℕ) : ∃ C, ∀ Y, ‖iteratedFDeriv ℝ k (Φ p) Y‖ ≤ C :=
    ((hΦ p).continuous_iteratedFDeriv (by simp)).bounded_above_of_compact_support
      ((hΦc p).iteratedFDeriv k)
  choose C hC using hBounds
  have hC0 (p k : ℕ) : 0 ≤ C p k := (norm_nonneg _).trans (hC p k 0)
  have hLineBounds (p : ℕ) : ∃ B, 0 ≤ B ∧
      ∀ t ∈ Icc 0 ε, ‖iteratedDeriv p F t‖ ≤ B := by
    have hcont := (contDiff_exponentialOrbit h π X hv).continuous_iteratedDeriv p (by simp)
    obtain ⟨B, hB⟩ := (isCompact_Icc.image hcont.norm).bddAbove
    exact ⟨max 0 B, le_max_left _ _, fun t ht =>
      (hB (mem_image_of_mem _ ht)).trans (le_max_right _ _)⟩
  choose B hB0 hB using hLineBounds
  let M : ℕ → ℝ := fun p => B p + ∑ k ∈ Finset.range (p + 1), C p k
  have hBM (p : ℕ) : B p ≤ M p :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hC0 p k)
  have hCM (p k : ℕ) (hk : k ≤ p) : C p k ≤ M p :=
    (Finset.single_le_sum (fun j _ => hC0 p j)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))).trans (le_add_of_nonneg_left (hB0 p))
  refine ⟨M, fun p t ht => (hB p t ht).trans (hBM p), fun c hc => ?_⟩
  have hu : Summable (fun p => (c p : ℂ) • u p) := by
    refine Summable.of_norm_bounded hc fun p => ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hB p 0 ⟨le_rfl, hε⟩).trans (hBM p)) (abs_nonneg _)
  refine ⟨hu, fun g => (h.contMDiffAt_iff_expG).2 ?_⟩
  have hs : ContDiff ℝ ∞ (fun Y => ∑' p, (c p : ℝ) • Φ p Y) := by
    refine contDiff_tsum (N := ⊤) (v := fun k p => |c p| * C p k)
      (fun p => (hΦ p).const_smul (c p)) ?_ ?_
    · intro k _
      apply (summable_nat_add_iff k).mp
      exact Summable.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (hC0 _ _))
        (fun p => mul_le_mul_of_nonneg_left (hCM _ _ (Nat.le_add_left k p)) (abs_nonneg _))
        ((summable_nat_add_iff k).2 hc)
    · intro k p Y _
      rw [iteratedFDeriv_const_smul_apply' ((hΦ p).contDiffAt.of_le (by simp)),
        norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC p k Y) (abs_nonneg _)
  refine (((π g).restrictScalars ℝ).contDiff.comp hs).contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds (0 : 𝔤) one_pos] with Y hY
  have hβ : β Y = 1 := β.one_of_mem_closedBall (ball_subset_closedBall hY)
  change π (g * h.expG Y) (∑' p, (c p : ℂ) • u p) = π g (∑' p, (c p : ℝ) • Φ p Y)
  rw [map_mul, mul_apply_eq_comp, (π (h.expG Y)).map_tsum hu]
  congr 1
  apply tsum_congr
  intro p
  simp only [Φ, hβ, one_smul, map_smul]
  rfl

private theorem exists_eq_two_exponentialAverages (X : 𝔤) {v : E} (hv : Smooth v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : E) (a b : ℝ → ℂ), Smooth w ∧ ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      tsupport a ⊆ Icc 0 ε ∧ tsupport b ⊆ Icc 0 ε ∧
      v = (∫ t, a t • exponentialOrbit h π X w t) +
        ∫ t, b t • exponentialOrbit h π X v t := by
  let F := exponentialOrbit h π X v
  have hF : ContDiff ℝ ∞ F := contDiff_exponentialOrbit h π X hv
  obtain ⟨M, hM, hSeries⟩ := exists_exponentialOrbit_bounds h π X hv ε hε.le
  obtain ⟨c, a, b, ha, hb, has, hbs, hc, hDirac⟩ :=
    exists_dirac_eq_tsum_iteratedDeriv_add M hε
  let w : E := ∑' p, (c p : ℂ) • iteratedDeriv p F 0
  obtain ⟨hSummable, hw⟩ := hSeries c hc
  have hac : HasCompactSupport a := isCompact_Icc.of_isClosed_subset (isClosed_tsupport a) has
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport b) hbs
  have hInt {u : E} (hu : Smooth u) {k : ℝ → ℂ} (hk : Continuous k)
      (hkc : HasCompactSupport k) : Integrable (fun t => k t • exponentialOrbit h π X u t) :=
    (hk.smul (contDiff_exponentialOrbit h π X hu).continuous).integrable_of_hasCompactSupport
      hkc.smul_right
  refine ⟨w, a, b, hw, ha, hb, has, hbs, eq_of_dual_unitBall fun L hL => ?_⟩
  have hcmp := iteratedDeriv_compCLM L (F := F) hF
  have hF0 : F 0 = v := by simp [F, exponentialOrbit]
  have hIdentity := hDirac (L ∘ F) ((L.restrictScalars ℝ).contDiff.comp hF)
    (fun p t ht => by
      rw [hcmp]
      calc ‖L (iteratedDeriv p F t)‖ ≤ ‖L‖ * ‖iteratedDeriv p F t‖ := L.le_opNorm _
        _ ≤ ‖iteratedDeriv p F t‖ := mul_le_of_le_one_left (norm_nonneg _) hL
        _ ≤ M p := hM p t ht)
  have hIdentity' : L v =
      (∑' p, (c p : ℂ) * ∫ t, L (iteratedDeriv p F t) * a t) + ∫ t, L (F t) * b t := by
    simpa only [hcmp, Function.comp_apply, hF0] using hIdentity
  rw [map_add, ← L.integral_comp_comm (hInt hw ha.continuous hac),
    ← L.integral_comp_comm (hInt hv hb.continuous hbc)]
  simp only [map_smul, smul_eq_mul]
  rw [hIdentity']
  congr 1
  · let Q : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (L (iteratedDeriv p F t) * a t)
    have hQ (p : ℕ) : Integrable (Q p) := by
      have hprod := (L.continuous.comp (hF.continuous_iteratedDeriv p (by simp))).mul ha.continuous
      exact (hprod.integrable_of_hasCompactSupport (μ := volume) hac.mul_left).const_mul _
    have hQa := (ha.continuous.integrable_of_hasCompactSupport (μ := volume) hac).norm
    have hQle (p : ℕ) (t : ℝ) : ‖Q p t‖ ≤ (|c p| * M p) * ‖a t‖ := by
      by_cases ht : t ∈ Icc 0 ε
      · simp only [Q, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          ((L.le_opNorm _).trans <| (mul_le_of_le_one_left (norm_nonneg _) hL).trans
            (hM p t ht)) (norm_nonneg _)) (abs_nonneg _)
      · have hzero : a t = 0 := by
          by_contra hn
          exact ht (has (subset_tsupport _ hn))
        simp [Q, hzero]
    have hQsum : Summable (fun p => ∫ t, ‖Q p t‖) := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, ‖a t‖))
      rw [← integral_const_mul]
      exact integral_mono (hQ p).norm (hQa.const_mul _) (hQle p)
    simp_rw [← integral_const_mul]
    change (∑' p, ∫ t, Q p t) = _
    rw [integral_tsum_of_summable_integral_norm hQ hQsum]
    apply integral_congr_ae
    filter_upwards with t
    have he : L (exponentialOrbit h π X w t) =
        ∑' p, (c p : ℂ) * L (iteratedDeriv p F t) := by
      change (L.comp (π (h.expG (t • X)))) w = _
      rw [(L.comp (π (h.expG (t • X)))).map_tsum hSummable]
      apply tsum_congr
      intro p
      rw [map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply,
        ← iteratedDeriv_exponentialOrbit h π X hv p t]
    rw [he, ← tsum_mul_left]
    apply tsum_congr
    intro p
    dsimp [Q]
    ring
  · exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)

private def inverseCoefficient (L : E →L[ℂ] ℂ) (v : E) (x : G) : ℂ :=
  L (π x⁻¹ v)

omit [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A] [CompleteSpace E] in
private theorem continuous_inverseCoefficient (hπ : IsContinuousRepresentation π)
    (L : E →L[ℂ] ℂ) (v : E) :
    Continuous (inverseCoefficient π L v) :=
  L.continuous.comp (hπ.comp (continuous_inv.prodMk continuous_const))

private theorem exists_eq_two_coefficientAverages (X : 𝔤) {v : E} (hv : Smooth v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : E) (a b : ℝ → ℂ), Smooth w ∧ ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      tsupport a ⊆ Icc (-ε) ε ∧ tsupport b ⊆ Icc (-ε) ε ∧
      ∀ (L : E →L[ℂ] ℂ) (x : G),
        inverseCoefficient π L v x =
          (∫ t, a t * inverseCoefficient π L w (h.expG (t • X) * x)) +
            ∫ t, b t * inverseCoefficient π L v (h.expG (t • X) * x) := by
  obtain ⟨w, a, b, hw, ha, hb, has, hbs, hEq⟩ :=
    exists_eq_two_exponentialAverages h π (-X) hv hε
  have hsub : Icc (0 : ℝ) ε ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) le_rfl
  refine ⟨w, a, b, hw, ha, hb, has.trans hsub, hbs.trans hsub, fun L x => ?_⟩
  have hInt {u : E} (hu : Smooth u) {k : ℝ → ℂ} (hk : ContDiff ℝ ∞ k)
      (hks : tsupport k ⊆ Icc 0 ε) :
      Integrable (fun t => k t • exponentialOrbit h π (-X) u t) := by
    have hkc : HasCompactSupport k := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hks
    exact (hk.continuous.smul (contDiff_exponentialOrbit h π (-X) hu).continuous)
      |>.integrable_of_hasCompactSupport hkc.smul_right
  let Lx := L.comp (π x⁻¹)
  have hArg (u : E) (t : ℝ) : Lx (exponentialOrbit h π (-X) u t) =
      inverseCoefficient π L u (h.expG (t • X) * x) := by
    change L (π x⁻¹ (π (h.expG (t • -X)) u)) = L (π ((h.expG (t • X) * x)⁻¹) u)
    rw [mul_inv_rev, ← h.expG_neg, map_mul, mul_apply_eq_comp, smul_neg]
  change Lx v = _
  have hLx := congrArg (fun u => Lx u) hEq
  rw [map_add, ← Lx.integral_comp_comm (hInt hw ha has),
    ← Lx.integral_comp_comm (hInt hv hb hbs)] at hLx
  simpa only [map_smul, smul_eq_mul, hArg] using hLx

private theorem exists_eq_sum_inverseCoefficients (hπ : IsContinuousRepresentation π)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ {d : ℕ} (X : Fin d → 𝔤) (v : E), Smooth v →
      ∃ (n : ℕ) (w : Fin n → E) (k : Fin n → (Fin d → ℝ) → ℂ),
        (∀ i, Smooth (w i) ∧ ContDiff ℝ ∞ (k i) ∧ tsupport (k i) ⊆ closedBall 0 ε) ∧
        ∀ (L : E →L[ℂ] ℂ) (x : G), inverseCoefficient π L v x =
          ∑ i, ∫ t, k i t * inverseCoefficient π L (w i) (h.revProdExp X t * x) := by
  intro d
  induction d with
  | zero =>
    intro X v hv
    refine ⟨1, fun _ => v, fun _ _ => 1, fun _ => ⟨hv, contDiff_const, ?_⟩, fun L x => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]
      exact mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [h.revProdExp_zero, hv]
  | succ d ih =>
    intro X v hv
    obtain ⟨u, a, b, hu, ha, hb, has, hbs, hEq⟩ :=
      exists_eq_two_coefficientAverages h π (X 0) hv hε
    obtain ⟨n₁, w₁, k₁, h₁, he₁⟩ := ih (Fin.tail X) u hu
    obtain ⟨n₂, w₂, k₂, h₂, he₂⟩ := ih (Fin.tail X) v hv
    refine ⟨n₁ + n₂, Fin.append w₁ w₂,
      Fin.append (fun i t => a (t 0) * k₁ i (Fin.tail t)) (fun i t => b (t 0) * k₂ i (Fin.tail t)),
      ?_, fun L x => ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using ⟨(h₁ j).1, contDiff_cons_kernel ha (h₁ j).2.1,
          tsupport_cons_kernel hε.le has (h₁ j).2.2⟩
      · simpa only [Fin.append_right] using ⟨(h₂ j).1, contDiff_cons_kernel hb (h₂ j).2.1,
          tsupport_cons_kernel hε.le hbs (h₂ j).2.2⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hEq L x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le ha.continuous has
          (fun i => (h₁ i).2.1.continuous) (fun i => (h₁ i).2.2)
          (fun i => continuous_inverseCoefficient π hπ L (w₁ i)) (he₁ L) x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hb.continuous hbs
          (fun i => (h₂ i).2.1.continuous) (fun i => (h₂ i).2.2)
          (fun i => continuous_inverseCoefficient π hπ L (w₂ i)) (he₂ L) x).symm

private theorem smoothVectorFactorization_exponentialCharts
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (hπ : IsContinuousRepresentation π) {U : Set G} (hU : U ∈ 𝓝 (1 : G))
    {v : E} (hv : Smooth v) :
    ∃ (n : ℕ) (w : Fin n → E) (k : Fin n → G → ℂ),
      (∀ i, Smooth (w i) ∧ (letI := h.chartedSpace; ContMDiff I 𝓘(ℝ, ℂ) ∞ (k i)) ∧
        HasCompactSupport (k i) ∧ tsupport (k i) ⊆ U ∧
        Integrable (fun g => k i g • π g (w i)) μ) ∧
      v = ∑ i, ∫ g, k i g • π g (w i) ∂μ := by
  let := h.chartedSpace
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε₀, hε₀, hdensity⟩ := h.exists_smooth_density_prodExp μ b
  have hP0 : h.prodExp (⇑b) 0 = 1 :=
    Subtype.ext (Units.ext (by rw [h.val_prodExp, prodExpVal_zero]; rfl))
  obtain ⟨ε₁, hε₁, hball⟩ := nhds_basis_closedBall.mem_iff.1
    ((h.continuous_prodExp (⇑b)).continuousAt.preimage_mem_nhds (t := U) (x := 0) (by rwa [hP0]))
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  obtain ⟨n, w, K, hK, hEq⟩ := exists_eq_sum_inverseCoefficients h π hπ hε (⇑b) v hv
  have hK' (i : Fin n) : ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ closedBall 0 ε := by
    refine ⟨(hK i).2.1.comp contDiff_neg, fun t ht => ?_⟩
    have ht' : -t ∈ tsupport (K i) :=
      tsupport_comp_subset_preimage (K i) (f := fun t => -t) continuous_neg ht
    simpa only [mem_closedBall_zero_iff, norm_neg] using (hK i).2.2 ht'
  choose k hks hkc hkV hk using
    fun i => hdensity ε (min_le_left _ _) (fun t => K i (-t)) (hK' i).1 (hK' i).2
  have hint (i : Fin n) : Integrable (fun g => k i g • π g (w i)) μ := by
    have hc := hπ.comp (continuous_id.prodMk (continuous_const (y := w i)))
    exact ((hks i).continuous.smul hc).integrable_of_hasCompactSupport (hkc i).smul_right
  refine ⟨n, w, k, fun i => ⟨(hK i).1, hks i, hkc i, (hkV i).trans
    (image_subset_iff.2 ((closedBall_subset_closedBall (min_le_right _ _)).trans hball)),
    hint i⟩, eq_of_dual_unitBall fun L _ => ?_⟩
  have hBase := hEq L 1
  simp only [inverseCoefficient, mul_one, inv_one, map_one, one_apply_eq_self] at hBase
  rw [hBase, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← L.integral_comp_comm (hint i)]
  let φ : G → ℂ := fun g => L (π g (w i))
  have hφ : Continuous φ :=
    L.continuous.comp (hπ.comp (continuous_id.prodMk continuous_const))
  simp only [map_smul, smul_eq_mul]
  change _ = ∫ g, k i g * φ g ∂μ
  rw [hk i φ hφ]
  have he (t : Fin (Module.finrank ℝ 𝔤) → ℝ) :
      K i (-t) * φ (h.prodExp (⇑b) t) =
        (fun s => K i s * φ (h.revProdExp (⇑b) s)⁻¹) (-t) := by
    have hv := h.revProdExp_inv (⇑b) (-t)
    rw [neg_neg] at hv
    change _ = K i (-t) * φ (h.revProdExp (⇑b) (-t))⁻¹
    rw [hv]
  simp_rw [he]
  exact (integral_neg_eq_self (fun t => K i t * φ (h.revProdExp (⇑b) t)⁻¹) volume).symm

end ExponentialCharts

/-- Factorization on the original group by transport through its closed linear realization. -/
theorem smoothVectorFactorization : SmoothVectorFactorizationStatement.{uA, uM, uG, uE} := by
  intro M _ _ G _ _ _ _ _ _ A _ _ _ _ j hj μ _ E _ _ _ π hπ U hU v hv
  let K := j.range
  let hK := hj.isExpLieAlgebra
  let e : G ≃ₜ* K := hj.rangeEquiv
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have : (μ.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  let π' := π.comp e.symm.toMonoidHom
  have hπ' : IsContinuousRepresentation π' :=
    hπ.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  have hv' : ExponentialSmoothVector hK π' v :=
    (hj.contMDiff_iff_comp_symm (orbitMap π v)).1 hv
  have hU' : e.symm ⁻¹' U ∈ 𝓝 (1 : K) :=
    e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨n, w, k, hk, hEq⟩ :=
    smoothVectorFactorization_exponentialCharts hK π' (μ.map e) hπ' hU' hv'
  have hkPull (i : Fin n) : (fun g => (k i ∘ e) g • π g (w i)) =
      (fun z : K => k i z • π' z (w i)) ∘ e := by
    funext g
    change k i (e g) • π g (w i) = k i (e g) • π (e.symm (e g)) (w i)
    rw [e.symm_apply_apply]
  have hμ (i : Fin n) :=
    integrable_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv
      (fun z : K => k i z • π' z (w i))
  have hκ (i : Fin n) : ContMDiff 𝓘(ℝ, M) 𝓘(ℝ, ℂ) ∞ (k i ∘ e) := by
    apply (hj.contMDiff_iff_comp_symm _).2
    have he : (k i ∘ e) ∘ e.symm = k i := by funext x; simp
    rw [he]
    exact (hk i).2.1
  refine ⟨n, w, fun i => k i ∘ e, fun i => ⟨
    (hj.contMDiff_iff_comp_symm (orbitMap π (w i))).2 (hk i).1,
    hκ i, (hk i).2.2.1.comp_homeomorph e.toHomeomorph, ?_, ?_⟩, ?_⟩
  · change tsupport (k i ∘ e.toHomeomorph) ⊆ U
    rw [tsupport_comp_eq_preimage (k i) e.toHomeomorph]
    intro g hg
    have hg' : e.symm (e g) ∈ U := (hk i).2.2.2.1 hg
    simpa only [e.symm_apply_apply] using hg'
  · rw [hkPull i]
    exact (hμ i).mp (hk i).2.2.2.2
  · rw [hEq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hkPull i]
    exact integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv _

end Langlands.Archimedean
