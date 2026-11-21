import Langlands.Global.RankinSelberg.ComplexBruhatTestExtension
import Langlands.Global.RankinSelberg.ComplexWhittakerSmoothExtension
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Restricting finite-order principal-series functionals to Gauss chart distributions -/

noncomputable section

open Filter Set TopologicalSpace WithSeminorms
open scoped Classical ContDiff Distributions Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatChartDistribution

open Langlands.Archimedean (continuous_unitary_toUnits)
open Langlands.Archimedean.UnitaryFinitePolynomial (compactSpace_unitary)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatGaussChart (chartDomain chartMatrixDomain chartCoordinates contDiffOn_chartCoordinates)
open ComplexBruhatTestExtension (ChartTest chartSaturation mem_chartSaturation isClosed_chartSaturation
  chartUnitMatrixDomain isOpen_chartUnitMatrixDomain chartUpperMatrix chartUpperMatrix_val
  inducingMultiplier contDiffOn_chartMultiplier extendTest extendTestMatrix extendTestMatrix_of_mem
  extendTestMatrix_zero)
open ComplexWhittakerSmoothExtension (SmoothStandard compactProfile)
open ComplexCompactSmoothDifferences (CompactProfileDifferenceBound complexCompactSmoothDifferences)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ

variable {n : ℕ}

private theorem contDiff_hasCompactSupport_cutoff {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {V U : Set (Mat n)} (hV : IsOpen V) (hUV : closure U ⊆ V) (hU : IsCompact (closure U))
    {η : Mat n → ℝ} (hη : ContDiff ℝ ∞ η) (hSupp : Function.support η = U)
    {f : Mat n → A} (hf : ContDiffOn ℝ ∞ f V) :
    ContDiff ℝ ∞ (fun X => η X • f X) ∧ HasCompactSupport (fun X => η X • f X) := by
  have hZero (X : Mat n) (hX : X ∉ U) : η X • f X = 0 :=
    (Function.notMem_support.mp (hSupp.symm ▸ hX)).symm ▸ zero_smul ℝ (f X)
  refine ⟨contDiff_iff_contDiffAt.mpr (fun X => ?_), ?_⟩
  · by_cases hX : X ∈ V
    · exact hη.contDiffAt.smul (hf.contDiffAt (hV.mem_nhds hX))
    · apply (contDiffAt_const (c := (0 : A))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (fun h => hX (hUV h))] with Y hY
      exact hZero Y (fun h => hY (subset_closure h))
  · exact HasCompactSupport.of_support_subset_isCompact hU
      (fun X hX => by_contra fun h => hX (hZero X (fun h' => h (subset_closure h'))))

private theorem exists_chart_extension_data (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    {S : Set (Coordinates n)} (hS : IsCompact S) :
    ∃ (m : Mat n → ℂ) (z : Mat n → Coordinates n),
      ContDiff ℝ ∞ m ∧ HasCompactSupport m ∧ ContDiff ℝ ∞ z ∧ HasCompactSupport z ∧
      ∀ φ : ChartTest n, tsupport φ ⊆ S → ∀ k : K n,
        m k.val * φ (z k.val) = compactProfile (extendTest w ds φ) k := by
  let : CompactSpace (K n) := compactSpace_unitary n
  let T := (fun k : K n => Unitary.toUnits k) ⁻¹' chartSaturation w S
  let M := (fun k : K n => k.val) '' T
  have hTc : IsClosed T := (isClosed_chartSaturation w hS).preimage continuous_unitary_toUnits
  have hMc : IsCompact M := hTc.isCompact.image continuous_subtype_val
  have hMV : M ⊆ chartUnitMatrixDomain w := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨(Unitary.toUnits k).isUnit, ((mem_chartSaturation w S (Unitary.toUnits k)).mp hk).1⟩
  obtain ⟨R, hR⟩ := hMc.exists_bound_of_continuousOn (continuous_id : Continuous fun X : Mat n => X).continuousOn
  let V := chartUnitMatrixDomain w ∩ Metric.ball 0 (R + 1)
  have hV : IsOpen V := (isOpen_chartUnitMatrixDomain w).inter Metric.isOpen_ball
  have hMV' : M ⊆ V := fun X hX =>
    ⟨hMV hX, mem_ball_zero_iff.mpr ((hR X hX).trans_lt (lt_add_one R))⟩
  obtain ⟨U, hU, hMU, hUV⟩ := hMc.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hMV')
  have hBound : ∀ {J : Set (Mat n)}, closure J ⊆ V → IsCompact (closure J) := fun hJ =>
    (isCompact_closedBall (0 : Mat n) (R + 1)).of_isClosed_subset isClosed_closure
      (hJ.trans fun _ h => Metric.ball_subset_closedBall h.2)
  obtain ⟨W, hW, hUW, hWV⟩ := (hBound hUV).exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hUV)
  obtain ⟨η, hη, _, hηSupp, hηOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU hMc.isClosed hMU
  obtain ⟨ρ, hρ, _, hρSupp, hρOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW isClosed_closure hUW
  let m (X : Mat n) := η X • inducingMultiplier ds (chartUpperMatrix w X)
  let z (X : Mat n) := ρ X • chartCoordinates w X
  have hO := isOpen_chartUnitMatrixDomain w
  obtain ⟨hm, hmCompact⟩ := contDiff_hasCompactSupport_cutoff hO (hUV.trans inter_subset_left)
    (hBound hUV) hη hηSupp (contDiffOn_chartMultiplier w ds)
  obtain ⟨hz, hzCompact⟩ := contDiff_hasCompactSupport_cutoff hO (hWV.trans inter_subset_left)
    (hBound hWV) hρ hρSupp ((contDiffOn_chartCoordinates w).mono inter_subset_right)
  refine ⟨m, z, hm, hmCompact, hz, hzCompact, fun φ hφ k => ?_⟩
  change m k.val * φ (z k.val) = extendTestMatrix w ds φ (Unitary.toUnits k).val
  by_cases hkt : k ∈ T
  · have hkM : k.val ∈ M := mem_image_of_mem _ hkt
    have hkc := ((mem_chartSaturation w S (Unitary.toUnits k)).mp hkt).1
    dsimp only [m, z]
    rw [(hηOne _).mp hkM, (hρOne _).mp (subset_closure (hMU hkM)),
      one_smul, one_smul, extendTestMatrix_of_mem w ds φ hkc, ← chartUpperMatrix_val]
    rfl
  · have hkφ : Unitary.toUnits k ∉ chartSaturation w (tsupport φ) := by
      intro hkφ
      obtain ⟨hkc, hp⟩ := (mem_chartSaturation w _ _).mp hkφ
      exact hkt ((mem_chartSaturation w _ _).mpr ⟨hkc, hφ hp⟩)
    rw [extendTestMatrix_zero w ds φ hkφ]
    by_cases hkU : k.val ∈ U
    · have hkv := hUV (subset_closure hkU)
      have hkc : Unitary.toUnits k ∈ chartDomain w := hkv.1.2
      have hkz : chartCoordinates w k.val ∉ tsupport φ := fun h =>
        hkφ ((mem_chartSaturation w _ _).mpr ⟨hkc, h⟩)
      dsimp only [z]
      rw [(hρOne _).mp (subset_closure hkU), one_smul,
        image_eq_zero_of_notMem_tsupport hkz, mul_zero]
    · have hη0 : η k.val = 0 := Function.notMem_support.mp (hηSupp.symm ▸ hkU)
      dsimp only [m]
      rw [hη0, zero_smul, zero_mul]

private abbrev CompactChartTest (S : Compacts (Coordinates n)) := 𝓓_{S}(Coordinates n, ℂ)

private def fullTest {S : Compacts (Coordinates n)} (φ : CompactChartTest S) : ChartTest n :=
  TestFunction.ofSupportedIn (show (S : Set (Coordinates n)) ⊆ (⊤ : Opens (Coordinates n)) from le_top) φ

private abbrev testSeminorm (S : Compacts (Coordinates n)) (J : ℕ) :=
  ContDiffMapSupportedIn.supSeminorm ℂ (Coordinates n) ℂ ⊤ S J

private theorem exists_bound_matrix_extension {S : Compacts (Coordinates n)} (J : ℕ)
    {m : Mat n → ℂ} {z : Mat n → Coordinates n}
    (hm : ContDiff ℝ ∞ m) (hmCompact : HasCompactSupport m)
    (hz : ContDiff ℝ ∞ z) (hzCompact : HasCompactSupport z) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (φ : CompactChartTest S) (j : ℕ), j ≤ J → ∀ X : Mat n,
      ‖iteratedFDeriv ℝ j (fun X => m X * φ (z X)) X‖ ≤ A * testSeminorm S J φ := by
  obtain ⟨M, hM, hMb⟩ := hmCompact.exists_bound_iteratedFDeriv hm J
  obtain ⟨D₀, _, hDb⟩ := hzCompact.exists_bound_iteratedFDeriv hz J
  let D := max 1 D₀
  have hD : 1 ≤ D := le_max_left _ _
  let P : ℝ := (J.factorial : ℝ) * D ^ J
  have hP : 0 ≤ P := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hD) _)
  let B : ℕ → ℝ := fun i => ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)
  have hB (i : ℕ) : 0 ≤ B i := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  let A : ℝ := (∑ i ∈ Finset.Iic J, B i) * M * P
  refine ⟨A, mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => hB i) hM) hP,
    fun φ j hj X => ?_⟩
  let q := testSeminorm S J φ
  have hq : 0 ≤ q := apply_nonneg _ _
  have hqBound (i : ℕ) (hi : i ≤ J) (Y : Coordinates n) : ‖iteratedFDeriv ℝ i φ Y‖ ≤ q :=
    (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
      (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr hi))
  have hComp (i : ℕ) (hi : i ≤ J) : ‖iteratedFDeriv ℝ i (⇑φ ∘ z) X‖ ≤ P * q := by
    have h := norm_iteratedFDeriv_comp_le φ.contDiff hz (n := i) (N := ∞) (by simp) X
      (C := q) (D := D) (fun k hk => hqBound k (hk.trans hi) _)
      (fun k hk hk' => (hDb k (hk'.trans hi) X).trans
        ((le_max_right 1 D₀).trans (le_self_pow₀ hD (by omega))))
    refine h.trans ?_
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (by exact_mod_cast Nat.factorial_le hi) (pow_le_pow_right₀ hD hi)
        (pow_nonneg (zero_le_one.trans hD) _) (Nat.cast_nonneg _)) hq
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i m X‖ *
        ‖iteratedFDeriv ℝ (j - i) (⇑φ ∘ z) X‖ :=
      norm_iteratedFDeriv_mul_le hm (φ.contDiff.comp hz) X (by simp)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M * (P * q) := by
      apply Finset.sum_le_sum
      intro i hi
      have hchoose : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hMb i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj) X) hchoose)
        (hComp (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (mul_nonneg hchoose hM)
    _ = B j * M * (P * q) := by simp only [B, Finset.sum_mul]
    _ ≤ A * q := by
      rw [show A * q = (∑ i ∈ Finset.Iic J, B i) * M * (P * q) by simp only [A, mul_assoc]]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_Iic.mpr hj)) hM)
        (mul_nonneg hP hq)

private theorem exists_bound_extendTest (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (S : Compacts (Coordinates n)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : CompactChartTest S,
      CompactProfileDifferenceBound J (compactProfile (extendTest w ds (fullTest φ))) (C * testSeminorm S J φ) := by
  obtain ⟨m, z, hm, hmCompact, hz, hzCompact, hEq⟩ := exists_chart_extension_data w ds S.isCompact
  obtain ⟨A, hA, hBound⟩ := exists_bound_matrix_extension (S := S) J hm hmCompact hz hzCompact
  obtain ⟨C, hC, hDiff⟩ := complexCompactSmoothDifferences n J
  refine ⟨C * A, mul_nonneg (zero_le_one.trans hC) hA, fun φ => ?_⟩
  have hEq' : compactProfile (extendTest w ds (fullTest φ)) = fun k : K n => m k.val * φ (z k.val) :=
    funext fun k => (hEq (fullTest φ) φ.tsupport_subset k).symm
  rw [hEq', mul_assoc]
  exact hDiff (fun X => m X * φ (z X)) _ (hm.mul (φ.contDiff.comp hz)) (mul_nonneg hA (apply_nonneg _ _))
    (fun j hj X _ => hBound φ j hj X)

/-- A functional of finite compact difference order gives a continuous complex-linear
functional on the chart test space. -/
def ComplexBruhatChartDistributionStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (w : Equiv.Perm (Fin n))
    (L : SmoothStandard n ds →ₗ[ℂ] ℂ) (J : ℕ) (C : ℝ), 0 ≤ C →
    (∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R) →
    ∃ T : ChartTest n →L[ℂ] ℂ, ∀ φ : ChartTest n, T φ = L (extendTest w ds φ)

theorem complexBruhatChartDistribution : ComplexBruhatChartDistributionStatement := by
  intro n ds w L J C _ hL
  let toFun (φ : ChartTest n) := L (extendTest w ds φ)
  have hS (S : Compacts (Coordinates n)) : ∃ T : CompactChartTest S →L[ℂ] ℂ,
      ∀ φ, T φ = toFun (fullTest φ) := by
    let I : CompactChartTest S →L[ℂ] ChartTest n := TestFunction.ofSupportedInCLM ℂ le_top
    let A := (L.comp (extendTest w ds)).comp I.toLinearMap
    obtain ⟨D, _, hD⟩ := exists_bound_extendTest w ds S J
    refine ⟨⟨A, (ContDiffMapSupportedIn.withSeminorms ..).continuous_of_isBounded
      (norm_withSeminorms ℂ ℂ) A (Seminorm.IsBounded.of_real fun _ => ?_)⟩, fun _ => rfl⟩
    refine ⟨Finset.Iic J, C * D, fun φ => ?_⟩
    change ‖L (extendTest w ds (fullTest φ))‖ ≤ (C * D) * testSeminorm S J φ
    rw [mul_assoc]
    exact hL _ _ (hD φ)
  exact ⟨TestFunction.limitCLM ℂ toFun (fun S _ => (hS S).choose)
    (fun S _ φ => ((hS S).choose_spec φ).symm), fun _ => rfl⟩

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatChartDistribution
