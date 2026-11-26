import Langlands.Analysis.DixmierMalliavin.Line
import Langlands.Geometry.Manifold.LinearLieGroup.Exponential
import Langlands.Representation.Archimedean.SmoothCompactOrbitIntegral
import Langlands.Representation.Archimedean.SmoothModerateGrowth
import Langlands.Representation.Archimedean.SmoothUnitActionDerivative
import Langlands.Representation.Archimedean.SmoothAction
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # One-parameter factorization of genuine smooth vectors -/

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Archimedean.DerivativeSmoothVectors

open Langlands.Analysis (hasDerivAt_iff_tendsto_slope_tvs)
open Langlands.Analysis.DixmierMalliavin (exists_dirac_eq_tsum_iteratedDeriv_add)
open Langlands.LinearLieGroup (expUnit continuous_expUnit)

universe uA uE

section Orbit

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R

/-- The genuine smooth orbit under the one-parameter subgroup of a direction. -/
def smoothExponentialOrbit (X : A) (v : D) (t : ℝ) : D :=
  representation I R (expUnit A (t • X)) v

omit [CompleteSpace E] in
private theorem continuous_smoothExponentialOrbit (hR : IsContinuousRepresentation R) (X : A) (v : D) :
    Continuous (smoothExponentialOrbit R X v) :=
  (continuous_representation_units R hR).comp
    (((continuous_expUnit A).comp (continuous_id.smul continuous_const)).prodMk continuous_const)

omit [FiniteDimensional ℝ A] [CompleteSpace E] in
private theorem smoothExponentialOrbit_zero (X : A) (v : D) : smoothExponentialOrbit R X v 0 = v := by
  have he : expUnit A ((0 : ℝ) • X) = 1 := by
    apply Units.ext
    simp
  rw [smoothExponentialOrbit, he, map_one, Module.End.one_apply]

omit [CompleteSpace E] in
private theorem hasDerivAt_smoothExponentialOrbit (hR : IsContinuousRepresentation R)
    (X : A) (v : D) (t : ℝ) : HasDerivAt (smoothExponentialOrbit R X v)
      (smoothExponentialOrbit R X (operator I R X v) t) t := by
  let g := expUnit A (t • X)
  have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  have h := hasDerivAt_unitsChartOrbit R hR g v hc rfl
  change HasDerivAt (fun u : ℝ => unitsChartAction R ((expUnit A (u • X)).val, v))
    (representation I R g (operator I R ((g⁻¹ : Aˣ).val * (g.val * X)) v)) t at h
  change HasDerivAt (fun u => representation I R (expUnit A (u • X)) v)
    (representation I R g (operator I R X v)) t
  simpa only [unitsChartAction_val, ← mul_assoc, Units.inv_mul, one_mul] using h

omit [CompleteSpace E] [FiniteDimensional ℝ A] in
private theorem hasDerivAt_scalar_of_smooth {f : ℝ → D} {w : D} {t : ℝ}
    (hf : HasDerivAt f w t) (L : D →L[ℂ] ℂ) : HasDerivAt (fun u => L (f u)) (L w) t := by
  apply hasDerivAt_iff_tendsto_slope_tvs.mpr
  let L₀ := L.restrictScalars ℝ
  refine ((L₀.continuous.tendsto w).comp (hasDerivAt_iff_tendsto_slope_tvs.mp hf)).congr ?_
  intro u
  simp [slope_def_module, map_sub, L₀]

private def directionalVectors (X : A) (v : D) : ℕ → D
  | 0 => v
  | p + 1 => operator I R X (directionalVectors X v p)

omit [CompleteSpace E] in
private theorem iteratedDeriv_smoothExponentialOrbit (hR : IsContinuousRepresentation R)
    (X : A) (v : D) (L : D →L[ℂ] ℂ) (p : ℕ) :
    iteratedDeriv p (fun t => L (smoothExponentialOrbit R X v t)) =
      fun t => L (smoothExponentialOrbit R X (directionalVectors R X v p) t) := by
  induction p with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ p ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_scalar_of_smooth R (hasDerivAt_smoothExponentialOrbit R hR X _ t) L).deriv

omit [CompleteSpace E] in
private theorem contDiff_scalarSmoothExponentialOrbit (hR : IsContinuousRepresentation R)
    (X : A) (v : D) (L : D →L[ℂ] ℂ) :
    ContDiff ℝ ∞ (fun t => L (smoothExponentialOrbit R X v t)) := by
  rw [contDiff_iff_iteratedDeriv]
  refine ⟨fun p _ => ?_, fun p _ t => ?_⟩
  · rw [iteratedDeriv_smoothExponentialOrbit R hR X v L]
    exact L.continuous.comp (continuous_smoothExponentialOrbit R hR X _)
  · rw [iteratedDeriv_smoothExponentialOrbit R hR X v L]
    exact (hasDerivAt_scalar_of_smooth R (hasDerivAt_smoothExponentialOrbit R hR X _ t) L).differentiableAt

omit [CompleteSpace E] in
private theorem exists_orderBounds (hR : IsContinuousRepresentation R) (X : A) (v : D) (ε : ℝ) :
    ∃ (B : ℕ → ℕ → ℝ), (∀ p k, 0 ≤ B p k) ∧
      ∀ p k t, t ∈ Icc 0 ε →
        wordOrderSeminorm R (Module.finBasis ℝ A) k
            (smoothExponentialOrbit R X (directionalVectors R X v p) t) ≤ B p k := by
  let b := Module.finBasis ℝ A
  have hb (p k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 ε,
      wordOrderSeminorm R b k (smoothExponentialOrbit R X (directionalVectors R X v p) t) ≤ C := by
    have hc := (continuous_wordOrderSeminorm R b k).comp
      (continuous_smoothExponentialOrbit R hR X (directionalVectors R X v p))
    obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).bddAbove
    exact ⟨max 0 C, le_max_left _ _, fun t ht => (hC (mem_image_of_mem _ ht)).trans (le_max_right _ _)⟩
  choose B hB hBound using hb
  exact ⟨B, hB, hBound⟩

omit [CompleteSpace E] in
private theorem exists_hasSum_of_wordwise (hR : IsContinuousRepresentation R) (f : ℕ → D)
    (hf : ∀ s, Summable (fun p => derivativeCLM I R s (f p))) : ∃ y : D, HasSum f y := by
  let coords := derivativeCoordinates I R
  let z : List A → E := fun s => ∑' p, derivativeCLM I R s (f p)
  have hs : HasSum (fun p => coords (f p)) z := Pi.hasSum.mpr fun s => (hf s).hasSum
  have hz : z ∈ range coords := by
    apply (isClosed_range_derivativeCoordinates_units R hR).mem_of_tendsto hs
    filter_upwards with J
    exact ⟨∑ p ∈ J, f p, by rw [map_sum]⟩
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, ?_⟩
  apply (isEmbedding_derivativeCoordinates I R).tendsto_nhds_iff.mpr
  change Tendsto (fun J => coords (∑ p ∈ J, f p)) _ (𝓝 (coords y))
  simpa only [HasSum, map_sum, hy] using hs

private theorem exists_weightedOrbit (hR : IsContinuousRepresentation R) (X : A) (v : D)
    (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ y : D, ∀ L : D →L[ℂ] ℂ, L y = ∫ t, g t * L (smoothExponentialOrbit R X v t) := by
  let f : ℝ → D := fun t => g t • smoothExponentialOrbit R X v t
  have hf := hg.smul (continuous_smoothExponentialOrbit R hR X v)
  obtain ⟨y, _, hY⟩ := smoothWordIntegral R volume hR f fun s => by
    have hc := (derivativeCLM I R s).continuous.comp hf
    have hcompact : HasCompactSupport (fun t => derivativeCLM I R s (f t)) := by
      simp only [f, map_smul]
      change HasCompactSupport (g • fun t => derivativeCLM I R s (smoothExponentialOrbit R X v t))
      exact hgc.smul_right
    exact hc.integrable_of_hasCompactSupport hcompact
  exact ⟨y, fun L => by simpa only [f, map_smul, smul_eq_mul] using (hY L).2⟩

end Orbit

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Aˣ →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R

/-- Along any real exponential direction, a smooth vector is the sum of two
smooth orbit averages with scalar kernels supported in a prescribed interval. -/
def SmoothVectorLineFactorizationStatement [FiniteDimensional ℝ A] [CompleteSpace E] : Prop :=
  IsContinuousRepresentation R →
    ∀ (X : A) (v : D) (ε : ℝ), 0 < ε →
      ∃ (w : D) (g k : ℝ → ℂ), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧
        tsupport g ⊆ Icc 0 ε ∧ tsupport k ⊆ Icc 0 ε ∧
        ∀ L : D →L[ℂ] ℂ,
          L v = (∫ t, g t * L (smoothExponentialOrbit R X w t)) +
            ∫ t, k t * L (smoothExponentialOrbit R X v t)

variable [FiniteDimensional ℝ A] [CompleteSpace E]

theorem smoothVectorLineFactorization : SmoothVectorLineFactorizationStatement R := by
  intro hR X v ε hε
  obtain ⟨B, hB, hb⟩ := exists_orderBounds R hR X v ε
  let M := fun p => 1 + ∑ k ∈ Finset.range (p + 1), B p k
  have hM (p k : ℕ) (hk : k ≤ p) : B p k ≤ M p := by
    have h := Finset.single_le_sum (f := fun j => B p j)
      (fun j _ => hB p j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨c, g, k, hg, hk, hgs, hks, hc, hDirac⟩ := exists_dirac_eq_tsum_iteratedDeriv_add M hε
  let u := directionalVectors R X v
  let q := fun p => (c p : ℂ) • u p
  have hWord (s : List A) (p : ℕ) :
      ‖derivativeCLM I R s (u p)‖ ≤
        (s.map fun Y => ‖Y‖).prod * B p s.length := by
    let basis := Module.finBasis ℝ A
    have hb₀ := hb p s.length 0 (show (0 : ℝ) ∈ Icc 0 ε from ⟨le_rfl, hε.le⟩)
    rw [smoothExponentialOrbit_zero] at hb₀
    have h := wordSeminormFamily_le_wordOrderSeminorm R basis s (u p)
    simp only [wordSeminormFamily_apply, ← derivativeCLM_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_left hb₀ (List.prod_nonneg (by simp)))
  obtain ⟨w, hw⟩ := exists_hasSum_of_wordwise R hR q (fun s => by
    let C := (s.map fun Y => ‖Y‖).prod
    have hC : 0 ≤ C := List.prod_nonneg (by simp)
    apply (summable_nat_add_iff s.length).mp
    refine Summable.of_norm_bounded ((summable_nat_add_iff s.length).mpr (hc.mul_right C)) ?_
    intro j
    let p := j + s.length
    change ‖derivativeCLM I R s ((c p : ℂ) • u p)‖ ≤ (|c p| * M p) * C
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |c p| * (C * B p s.length) :=
        mul_le_mul_of_nonneg_left (hWord s p) (abs_nonneg _)
      _ ≤ |c p| * (C * M p) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hM p _ (Nat.le_add_left _ _)) hC) (abs_nonneg _)
      _ = _ := by ring)
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hgs
  have hkc : HasCompactSupport k := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hks
  obtain ⟨y, hy⟩ := exists_weightedOrbit R hR X w g hg.continuous hgc
  obtain ⟨z, hz⟩ := exists_weightedOrbit R hR X v k hk.continuous hkc
  have hCompare (ell : E →L[ℂ] ℂ) (hell : ‖ell‖ ≤ 1) :
      (ell.comp (derivativeCLM I R [])) v =
        (ell.comp (derivativeCLM I R [])) y + (ell.comp (derivativeCLM I R [])) z := by
    let L := ell.comp (derivativeCLM I R [])
    let F := fun p t => L (smoothExponentialOrbit R X (u p) t)
    have hFcont (p : ℕ) : Continuous (F p) := L.continuous.comp
      (continuous_smoothExponentialOrbit R hR X (u p))
    have hFbound (p : ℕ) (t : ℝ) (ht : t ∈ Icc 0 ε) : ‖F p t‖ ≤ M p := by
      let e := derivativeCLM I R [] (smoothExponentialOrbit R X (u p) t)
      have h₀ : ‖e‖ ≤ B p 0 := by
        simpa only [e, u, wordOrderSeminorm, wordSeminormFamily_apply,
          derivativeCLM_apply] using hb p 0 t ht
      calc ‖F p t‖ ≤ ‖ell‖ * ‖e‖ := ell.le_opNorm _
        _ ≤ 1 * ‖e‖ := mul_le_mul_of_nonneg_right hell (norm_nonneg _)
        _ ≤ M p := by rw [one_mul]; exact h₀.trans (hM p 0 (Nat.zero_le p))
    have hDir := hDirac (F 0) (contDiff_scalarSmoothExponentialOrbit R hR X v L)
      (fun p t ht => by
        rw [show F 0 = (fun t => L (smoothExponentialOrbit R X v t)) from rfl,
          iteratedDeriv_smoothExponentialOrbit R hR X v L]
        exact hFbound p t ht)
    change L v = L y + L z
    rw [hy L, hz L]
    have hD (p : ℕ) : iteratedDeriv p (F 0) = F p :=
      iteratedDeriv_smoothExponentialOrbit R hR X v L p
    simp_rw [hD] at hDir
    have h0 : F 0 0 = L v := congrArg L (smoothExponentialOrbit_zero R X v)
    rw [h0] at hDir
    let K := fun p t => (c p : ℂ) * (F p t * g t)
    have hKi (p : ℕ) : Integrable (K p) :=
      (((hFcont p).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left).const_mul _
    have hGn : Integrable (fun t => ‖g t‖) := (hg.continuous.integrable_of_hasCompactSupport hgc).norm
    have hKbound (p : ℕ) (t : ℝ) : ‖K p t‖ ≤ |c p| * M p * ‖g t‖ := by
      by_cases ht : t ∈ Icc 0 ε
      · simp only [K, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hFbound p t ht) (norm_nonneg _))
          (abs_nonneg _)
      · have hgt : g t = 0 := by
          by_contra hne
          exact ht (hgs (subset_tsupport _ hne))
        simp [K, hgt]
    have hsum : Summable (fun p => ∫ t, ‖K p t‖) := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, ‖g t‖))
      rw [← integral_const_mul]
      exact integral_mono (hKi p).norm (hGn.const_mul _) (hKbound p)
    have hIntegral : (∑' p, (c p : ℂ) * ∫ t, F p t * g t) =
        ∫ t, g t * L (smoothExponentialOrbit R X w t) := by
      simp_rw [← integral_const_mul]
      change (∑' p, ∫ t, K p t) = _
      rw [integral_tsum_of_summable_integral_norm hKi hsum]
      apply integral_congr_ae
      filter_upwards with t
      let T := L.comp (SmoothAction.derivativeAction I R (expUnit A (t • X)))
      have ht := T.hasSum hw
      have hAction (q : D) : SmoothAction.derivativeAction I R (expUnit A (t • X)) q =
          smoothExponentialOrbit R X q t := by
        apply (toSmooth I R).injective
        simp only [SmoothAction.toSmooth_derivativeAction, smoothExponentialOrbit, toSmooth_representation]
      have he : (∑' p, (c p : ℂ) * F p t) = L (smoothExponentialOrbit R X w t) := by
        apply HasSum.tsum_eq
        simpa only [q, map_smul, smul_eq_mul, T, F, ContinuousLinearMap.comp_apply, hAction] using ht
      rw [← he, ← tsum_mul_left]
      exact tsum_congr fun p => by dsimp [K]; ring
    rw [hIntegral] at hDir
    change L v = _ + ∫ t, k t * F 0 t
    simpa only [mul_comm (F 0 _) (k _)] using hDir
  have hEq : v = y + z := by
    let P := derivativeCLM I R []
    have hP : Function.Injective P := by
      intro x₁ x₂ h
      apply (toSmooth I R).injective
      apply Subtype.ext
      simpa only [P, derivativeCLM_apply, iteratedLieDerivative_nil] using h
    apply hP
    by_contra hne
    obtain ⟨a, ha, hsep⟩ := exists_dual_vector ℂ (P v - P (y + z))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
    have hv := hCompare a ha.le
    change a (P v) = a (P y) + a (P z) at hv
    rw [map_sub, map_add, map_add, hv, sub_self] at hsep
    exact (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))) hsep.symm
  refine ⟨w, g, k, hg, hk, hgs, hks, fun L => ?_⟩
  calc
    L v = L (y + z) := congrArg L hEq
    _ = _ := by rw [map_add, hy, hz]

end Langlands.Archimedean.DerivativeSmoothVectors
