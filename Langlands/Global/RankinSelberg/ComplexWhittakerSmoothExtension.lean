import Langlands.Global.RankinSelberg.ComplexCompactDifferenceDensity
import Langlands.Global.RankinSelberg.ComplexWhittakerFiniteOrder
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Extending exact complex Whittaker identity evaluation to smooth sections -/

noncomputable section

open Filter Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexWhittakerSmoothExtension

open Langlands.Archimedean (complexStandardModule contDiffOn_unitsExtension isOpen_setOf_isUnit_matrix
  matrixModel unitsExtension unitsExtension_val)
open Langlands.Archimedean.UnitaryFinitePolynomial (isCompact_unitary)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactDifferenceDensity (complexCompactDifferenceDensity)
open ComplexCompactDifferences (displacementProduct displacementProduct_nonneg)
open ComplexCompactSmoothDifferences (compactFunctionDifference CompactProfileDifferenceBound
  compactDifferenceBound_iff complexCompactSmoothDifferences)
open ComplexWhittakerFiniteOrder (complexWhittakerFiniteOrder)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

variable {n : ℕ} {ds : List ComplexCharacterData}

/-- Smooth standard sections before imposing compact finiteness. -/
abbrev SmoothStandard (n : ℕ) (ds : List ComplexCharacterData) := complexStandardModule n ds

/-- Inclusion of compact-finite standard vectors into the smooth principal series. -/
def finiteToSmooth : Std n ds →ₗ[ℂ] SmoothStandard n ds :=
  (Std n ds).subtype.codRestrict _ fun f => f.2.1

/-- Restriction of a smooth standard vector to the unitary matrix group. -/
def compactProfile : SmoothStandard n ds →ₗ[ℂ] (K n → ℂ) :=
  LinearMap.pi fun x => (LinearMap.proj (Unitary.toUnits x)).comp (SmoothStandard n ds).subtype

/-- A smooth function on the invertible matrices has a compactly supported smooth matrix
extension agreeing with it on any given compact subset of invertible matrices. -/
theorem exists_smooth_matrix_extension {S : Set (Mat n)} (hS : IsCompact S)
    (hUnit : ∀ x ∈ S, IsUnit x) {F : G n → ℂ} (hF : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ F) :
    ∃ H : Mat n → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ g : G n, g.val ∈ S → H g.val = F g := by
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn (continuous_id : Continuous fun x : Mat n => x).continuousOn
  let V := {x : Mat n | IsUnit x} ∩ Metric.ball 0 (R + 1)
  have hV : IsOpen V := isOpen_setOf_isUnit_matrix.inter Metric.isOpen_ball
  have hSV : S ⊆ V := fun x hx => ⟨hUnit x hx, mem_ball_zero_iff.mpr ((hR x hx).trans_lt (lt_add_one R))⟩
  obtain ⟨U, hU, hSU, hUV⟩ := hS.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hSV)
  obtain ⟨c, hc, _, hcSupp, hcOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU hS.isClosed hSU
  let H (x : Mat n) := c x • unitsExtension F x
  have hcZero (x : Mat n) (hx : x ∉ U) : c x = 0 := by
    have h : x ∉ Function.support c := fun h => hx (hcSupp ▸ h)
    simpa only [Function.mem_support, not_not] using h
  have hHZero (x : Mat n) (hx : x ∉ U) : H x = 0 := by simp only [H, hcZero x hx, zero_smul]
  have hSupp : tsupport H ⊆ closure U := closure_mono (fun x hx => by
    by_contra hn
    exact hx (hHZero x hn))
  have hCompact : HasCompactSupport H := by
    apply (isCompact_closedBall (0 : Mat n) (R + 1)).of_isClosed_subset (isClosed_tsupport H)
    exact hSupp.trans (hUV.trans (fun _ hx => Metric.ball_subset_closedBall hx.2))
  refine ⟨H, ?_, hCompact, fun g hg => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hu : IsUnit x
    · exact hc.contDiffAt.smul ((contDiffOn_unitsExtension hF).contDiffAt
        (isOpen_setOf_isUnit_matrix.mem_nhds hu))
    · have hx : x ∉ closure U := fun hx => hu (hUV hx).1
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      exact hHZero y (fun hyU => hy (subset_closure hyU))
  · change c g.val • unitsExtension F g.val = F g
    rw [(hcOne _).mp hg, one_smul, unitsExtension_val]

theorem exists_smooth_compact_difference_bound {F : G n → ℂ}
    (hF : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ F) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ CompactProfileDifferenceBound J (fun k => F (Unitary.toUnits k)) D := by
  have hk (x : Mat n) (hx : x ∈ Matrix.unitaryGroup (Fin n) ℂ) : IsUnit x :=
    (Unitary.toUnits (⟨x, hx⟩ : K n)).isUnit
  obtain ⟨H, hH, hc, hAgree⟩ := exists_smooth_matrix_extension (isCompact_unitary n) hk hF
  obtain ⟨D, hD, hBound⟩ := hc.exists_bound_iteratedFDeriv hH J
  obtain ⟨C, hC, hDiff⟩ := complexCompactSmoothDifferences n J
  refine ⟨C * D, mul_nonneg (zero_le_one.trans hC) hD, ?_⟩
  have hEq : (fun k : K n => F (Unitary.toUnits k)) = fun k => H k.val :=
    funext fun k => (hAgree (Unitary.toUnits k) k.2).symm
  rw [hEq]
  exact hDiff H D hH hD (fun i hi x _ => hBound i hi x)

private def differenceLinear (ks : List (K n)) : Module.End ℂ (K n → ℂ) :=
  ks.foldr (fun k T => (LinearMap.pi (fun x : K n =>
    LinearMap.proj (R := ℂ) (φ := fun _ : K n => ℂ) (x * k) - LinearMap.proj x)) ∘ₗ T) 1

private theorem differenceLinear_apply (ks : List (K n)) (φ : K n → ℂ) :
    differenceLinear ks φ = compactFunctionDifference ks φ := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    funext x
    change differenceLinear ks φ (x * k) - differenceLinear ks φ x = _
    rw [ih]
    rfl

private theorem bound_zero {J : ℕ} : CompactProfileDifferenceBound (n := n) J 0 0 := by
  intro ks _ x
  rw [← differenceLinear_apply, map_zero, Pi.zero_apply, norm_zero, zero_mul]

private theorem bound_add {J : ℕ} {φ ψ : K n → ℂ} {D E : ℝ}
    (hφ : CompactProfileDifferenceBound J φ D) (hψ : CompactProfileDifferenceBound J ψ E) :
    CompactProfileDifferenceBound J (φ + ψ) (D + E) := by
  intro ks hks x
  rw [← differenceLinear_apply, map_add, Pi.add_apply, differenceLinear_apply, differenceLinear_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hφ _ hks _) (hψ _ hks _))

private theorem bound_sub {J : ℕ} {φ ψ : K n → ℂ} {D E : ℝ}
    (hφ : CompactProfileDifferenceBound J φ D) (hψ : CompactProfileDifferenceBound J ψ E) :
    CompactProfileDifferenceBound J (φ - ψ) (D + E) := by
  intro ks hks x
  rw [← differenceLinear_apply, map_sub, Pi.sub_apply, differenceLinear_apply, differenceLinear_apply, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hφ _ hks _) (hψ _ hks _))

private theorem bound_smul {J : ℕ} {φ : K n → ℂ} {D : ℝ}
    (hφ : CompactProfileDifferenceBound J φ D) (z : ℂ) : CompactProfileDifferenceBound J (z • φ) (‖z‖ * D) := by
  intro ks hks x
  rw [← differenceLinear_apply, map_smul, Pi.smul_apply, norm_smul, differenceLinear_apply, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hφ _ hks _) (norm_nonneg _)

private theorem exists_nearby_finite (F : SmoothStandard n ds) (J : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Std n ds, CompactProfileDifferenceBound J (compactProfile (finiteToSmooth f) - compactProfile F) ε := by
  obtain ⟨D, hD, hDiff⟩ := exists_smooth_compact_difference_bound F.2.1 (J + 1)
  have hpos : 0 < D + 1 := by positivity
  obtain ⟨f, hf⟩ := complexCompactDifferenceDensity n ds F.val F.2 J D (ε / (D + 1)) hD
    (div_pos hε hpos) hDiff
  have hbound : D * (ε / (D + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hpos, mul_comm D ε]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hε.le
  exact ⟨f, fun ks hks x => (hf ks hks x).trans (mul_le_mul_of_nonneg_right hbound
    (displacementProduct_nonneg ks))⟩

/-- Exact complex Whittaker identity evaluation extends linearly to smooth standard sections
with the same finite-order compact difference bound. -/
def ComplexWhittakerSmoothExtensionStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∃ (L : SmoothStandard (r + 1) ds →ₗ[ℂ] ℂ) (J : ℕ) (C : ℝ), 0 ≤ C ∧
    (∀ f : Std (r + 1) ds, L (finiteToSmooth f) = B f 1) ∧
    ∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R

set_option maxHeartbeats 900000 in
theorem complexWhittakerSmoothExtension : ComplexWhittakerSmoothExtensionStatement := by
  intro r ds a B hB
  let n := r + 1
  let ℓ : Std n ds →ₗ[ℂ] ℂ := (LinearMap.proj 1).comp B
  let φ : SmoothStandard n ds →ₗ[ℂ] (K n → ℂ) := compactProfile
  let ρ := φ.comp (finiteToSmooth : Std n ds →ₗ[ℂ] SmoothStandard n ds)
  obtain ⟨J, C, hC, hBnd⟩ := complexWhittakerFiniteOrder r ds a B hB
  have hEval (f : Std n ds) (R : ℝ) (hR : CompactProfileDifferenceBound J (ρ f) R) :
      ‖ℓ f‖ ≤ C * R := hBnd f R ((compactDifferenceBound_iff f J R).mpr hR)
  have compare (F : SmoothStandard n ds) (f g : Std n ds) (S T : ℝ)
      (hS : CompactProfileDifferenceBound J (ρ f - φ F) S)
      (hT : CompactProfileDifferenceBound J (ρ g - φ F) T) : ‖ℓ f - ℓ g‖ ≤ C * (S + T) := by
    rw [← map_sub ℓ]
    apply hEval _ _
    rw [map_sub, ← show (ρ f - φ F) - (ρ g - φ F) = ρ f - ρ g by abel]
    exact bound_sub hS hT
  let e (i : ℕ) := (1 / 2 : ℝ) ^ i
  have he (i : ℕ) : 0 < e i := pow_pos (by norm_num) _
  have heAnti : Antitone e := fun i j hij => pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
  have heLim : Tendsto e atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  choose f hf using fun (F : SmoothStandard n ds) (i : ℕ) => exists_nearby_finite F J (he i)
  have hcauchy (F : SmoothStandard n ds) : CauchySeq (fun i => ℓ (f F i)) := by
    refine cauchySeq_iff_le_tendsto_0.mpr ⟨fun i => C * (e i + e i), fun i => by positivity, ?_, ?_⟩
    · intro i j N hi hj
      rw [dist_eq_norm]
      exact (compare F _ _ _ _ (hf F i) (hf F j)).trans
        (mul_le_mul_of_nonneg_left (add_le_add (heAnti hi) (heAnti hj)) hC)
    · simpa only [zero_add, mul_zero] using (heLim.add heLim).const_mul C
  choose L hL using fun F => cauchySeq_tendsto_of_complete (hcauchy F)
  have limit_of_approx (F : SmoothStandard n ds) (g : ℕ → Std n ds) (s : ℕ → ℝ)
      (hs : Tendsto s atTop (𝓝 0)) (hg : ∀ i, CompactProfileDifferenceBound J (ρ (g i) - φ F) (s i)) :
      Tendsto (fun i => ℓ (g i)) atTop (𝓝 (L F)) := by
    have hLim : Tendsto (fun i => C * (s i + e i)) atTop (𝓝 0) := by
      simpa only [zero_add, mul_zero] using (hs.add heLim).const_mul C
    have hd : Tendsto (fun i => ℓ (g i) - ℓ (f F i)) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
        (fun i => compare F _ _ _ _ (hg i) (hf F i)) hLim)
    simpa only [sub_add_cancel, zero_add] using hd.add (hL F)
  let Λ : SmoothStandard n ds →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' F F' := by
        have hApp (i : ℕ) : CompactProfileDifferenceBound J (ρ (f F i + f F' i) - φ (F + F')) (e i + e i) := by
          rw [map_add, map_add, show ρ (f F i) + ρ (f F' i) - (φ F + φ F') =
            (ρ (f F i) - φ F) + (ρ (f F' i) - φ F') by abel]
          exact bound_add (hf F i) (hf F' i)
        apply tendsto_nhds_unique (limit_of_approx (F + F') (fun i => f F i + f F' i)
          (fun i => e i + e i) (by simpa only [zero_add] using heLim.add heLim) hApp)
        simpa only [map_add] using (hL F).add (hL F')
      map_smul' z F := by
        have hApp (i : ℕ) : CompactProfileDifferenceBound J (ρ (z • f F i) - φ (z • F)) (‖z‖ * e i) := by
          rw [map_smul, map_smul, ← smul_sub]
          exact bound_smul (hf F i) z
        apply tendsto_nhds_unique (limit_of_approx (z • F) (fun i => z • f F i)
          (fun i => ‖z‖ * e i) (by simpa only [mul_zero] using heLim.const_mul ‖z‖) hApp)
        simpa only [map_smul, RingHom.id_apply, smul_eq_mul] using (hL F).const_mul z }
  refine ⟨Λ, J, C, hC, ?_, ?_⟩
  · intro u
    have hApp (i : ℕ) : CompactProfileDifferenceBound J (ρ u - φ (finiteToSmooth u)) 0 := by
      change CompactProfileDifferenceBound J (ρ u - ρ u) 0
      rw [sub_self]
      exact bound_zero
    exact tendsto_nhds_unique (limit_of_approx (finiteToSmooth u) (fun _ => u) (fun _ => 0)
      tendsto_const_nhds hApp) tendsto_const_nhds
  · intro F R hR
    have hApp (i : ℕ) : CompactProfileDifferenceBound J (ρ (f F i)) (e i + R) := by
      have hh := bound_add (hf F i) hR
      rw [sub_add_cancel] at hh
      exact hh
    have hLim : Tendsto (fun i => C * (e i + R)) atTop (𝓝 (C * R)) := by
      simpa only [zero_add] using (heLim.add_const R).const_mul C
    exact le_of_tendsto_of_tendsto' (hL F).norm hLim (fun i => hEval _ _ (hApp i))

end Langlands.Global.RankinSelbergGlobal.ComplexWhittakerSmoothExtension
