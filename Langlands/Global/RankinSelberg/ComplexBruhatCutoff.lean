import Langlands.Global.RankinSelberg.ComplexBruhatChartDerivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Borel-invariant cutoffs and restriction in complex Gauss charts -/

noncomputable section

open Set Filter TopologicalSpace
open scoped Classical ContDiff Distributions Manifold Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatCutoff

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.GeneralLinear (upperTriangularSubgroup diagonalUnits_mem_upperTriangular
  upperUnipotent_le_upperTriangular)
open Langlands.Archimedean (borelFactor posWeight posExponent posWeight_ofFn posExponent_ofFn
  characterOfParams characterOfParams_weight characterOfParams_exponent complexPositionCharacter
  mem_principalSeries_iff contMDiff_of_contDiffOn contDiffOn_unitsExtension unitsExtension_val)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatGaussChart (chartDomain chartCoordinates chartSection chartUpper
  isOpen_chartDomain contDiffOn_chartCoordinates continuous_chartSection chart_recover chart_factorization
  chartUpper_mem)
open ComplexBruhatTestExtension (ChartTest chartSaturation mem_chartSaturation extendTest extendTest_apply
  extendTestMatrix_of_mem inducingMultiplier tsupport_extendTest_subset)
open ComplexBruhatChartDerivative (standard_borel_covariance standard_chart_covariance contDiff_chartSection_val)
open ComplexWhittakerSmoothExtension (SmoothStandard)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "B" => fun n => upperTriangularSubgroup n ℂ

variable {n : ℕ} {ds : List ComplexCharacterData}

/-- Inducing parameters whose normalized Borel multiplier is identically one. -/
def neutralData (n : ℕ) : List ComplexCharacterData :=
  List.ofFn fun i : Fin n => characterOfParams 0 (-(((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)))

@[simp] theorem inducingMultiplier_neutral (X : Mat n) : inducingMultiplier (neutralData n) X = 1 := by
  change (∏ i : Fin n, borelFactor (posWeight (neutralData n) i)
    (2 * (posExponent (neutralData n) i + (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)))) (X i i)) = 1
  simp [neutralData, posWeight_ofFn, posExponent_ofFn, borelFactor]

/-- The scalar cutoff associated with a compactly supported test in a Gauss chart. -/
def chartCutoff (w : Equiv.Perm (Fin n)) (η : ChartTest n) : G n → ℂ :=
  (extendTest w (neutralData n) η).val

@[simp] theorem chartCutoff_left_mul (w : Equiv.Perm (Fin n)) (η : ChartTest n) (b : B n) (g : G n) :
    chartCutoff w η (b.val * g) = chartCutoff w η g := by
  exact (standard_borel_covariance (extendTest w (neutralData n) η) b g).trans (by simp [chartCutoff])

theorem chartCutoff_apply_of_mem (w : Equiv.Perm (Fin n)) (η : ChartTest n) {g : G n}
    (hg : g ∈ chartDomain w) : chartCutoff w η g = η (chartCoordinates w g.val) := by
  rw [chartCutoff, extendTest_apply, extendTestMatrix_of_mem w _ _ hg, inducingMultiplier_neutral, one_mul]

theorem tsupport_chartCutoff_subset (w : Equiv.Perm (Fin n)) (η : ChartTest n) :
    tsupport (chartCutoff w η) ⊆ chartSaturation w (tsupport η) :=
  tsupport_extendTest_subset w (neutralData n) η

theorem chartSaturation_mono (w : Equiv.Perm (Fin n)) {S U : Set (Coordinates n)} (h : S ⊆ U) :
    chartSaturation w S ⊆ chartSaturation w U :=
  fun _ ⟨z, hz, hb⟩ => ⟨z, h hz, hb⟩

theorem chartSection_mem_chartSaturation_iff (w : Equiv.Perm (Fin n)) (S : Set (Coordinates n))
    (z : Coordinates n) : chartSection w z ∈ chartSaturation w S ↔ z ∈ S := by
  obtain ⟨hd, hc, _⟩ := chart_recover w (1 : B n) z
  simp only [Subgroup.coe_one, one_mul] at hd hc
  rw [mem_chartSaturation, hc]
  exact and_iff_right hd

/-- A test with compact support in the chart can equal one in a neighborhood of any
point in its saturation. -/
theorem exists_chartCutoff (w : Equiv.Perm (Fin n)) {O : Set (Coordinates n)} (hO : IsOpen O)
    {g : G n} (hg : g ∈ chartSaturation w O) :
    ∃ η : ChartTest n, tsupport η ⊆ O ∧ chartCutoff w η =ᶠ[𝓝 g] 1 := by
  obtain ⟨hg, hz⟩ := (mem_chartSaturation w O g).mp hg
  let z := chartCoordinates w g.val
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hz)
  let b : ContDiffBump z := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let f : Coordinates n → ℂ := fun y => (b y : ℂ)
  have hf : tsupport f ⊆ tsupport b := by
    apply closure_mono
    intro y hy
    exact fun h => hy (by simp [f, h])
  let η : ChartTest n := ⟨f, Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hf, subset_univ _⟩
  refine ⟨η, hf.trans (b.tsupport_eq ▸ hball), ?_⟩
  have hCoord : ContinuousAt (fun g : G n => chartCoordinates w g.val) g :=
    ((contDiffOn_chartCoordinates w).contDiffAt
      ((ComplexBruhatGaussChart.isOpen_chartMatrixDomain w).mem_nhds hg)).continuousAt.comp
        Units.continuous_val.continuousAt
  filter_upwards [(isOpen_chartDomain w).mem_nhds hg,
    hCoord.eventually (b.eventuallyEq_one : (b : Coordinates n → ℝ) =ᶠ[𝓝 z] 1)] with y hy hby
  rw [chartCutoff_apply_of_mem w η hy]
  change (b (chartCoordinates w y.val) : ℂ) = 1
  change b (chartCoordinates w y.val) = 1 at hby
  simp [hby]

/-- Multiplying by an invariant cutoff preserves the exact principal series. -/
def cutoffSection (w : Equiv.Perm (Fin n)) (η : ChartTest n) (F : SmoothStandard n ds) :
    SmoothStandard n ds := by
  let c := extendTest w (neutralData n) η
  have hc := ((mem_principalSeries_iff ℂ n (complexPositionCharacter (neutralData n)) c.val).mp c.2).1
  have hF := (mem_principalSeries_iff ℂ n (complexPositionCharacter ds) F.val).mp F.2
  refine ⟨fun g => chartCutoff w η g * F.val g, (mem_principalSeries_iff ℂ n
    (complexPositionCharacter ds) _).mpr ⟨?_, ?_⟩⟩
  · exact contMDiff_of_contDiffOn ((contDiffOn_unitsExtension hc).mul (contDiffOn_unitsExtension hF.1))
      (fun g => by simp only [unitsExtension_val]; rfl)
  · intro a u g
    let b : B n := ⟨Langlands.GeneralLinear.Iwasawa.diagonalUnits a * u.val,
      mul_mem (diagonalUnits_mem_upperTriangular n a) (upperUnipotent_le_upperTriangular n ℂ u.2)⟩
    change chartCutoff w η (b.val * g) * F.val (b.val * g) = _
    rw [chartCutoff_left_mul, hF.2 a u g]
    ring

@[simp] theorem cutoffSection_apply (w : Equiv.Perm (Fin n)) (η : ChartTest n) (F : SmoothStandard n ds)
    (g : G n) : (cutoffSection w η F).val g = chartCutoff w η g * F.val g := rfl

theorem tsupport_cutoffSection_subset (w : Equiv.Perm (Fin n)) (η : ChartTest n) (F : SmoothStandard n ds) :
    tsupport (cutoffSection w η F).val ⊆ chartSaturation w (tsupport η) :=
  (show tsupport (fun g => chartCutoff w η g * F.val g) ⊆ tsupport (chartCutoff w η) from
    tsupport_mul_subset_left).trans (tsupport_chartCutoff_subset w η)

/-- A section supported over a compact subset of the chart is the extension of its
restriction to the chart representatives. -/
theorem exists_chartTest_of_tsupport (w : Equiv.Perm (Fin n)) {S : Set (Coordinates n)}
    (hS : IsCompact S) (F : SmoothStandard n ds) (hF : tsupport F.val ⊆ chartSaturation w S) :
    ∃ φ : ChartTest n, tsupport φ ⊆ S ∧ extendTest w ds φ = F := by
  let f : Coordinates n → ℂ := F.val ∘ chartSection w
  have hSupp : tsupport f ⊆ S := fun z hz =>
    (chartSection_mem_chartSaturation_iff w S z).mp
      (hF (tsupport_comp_subset_preimage F.val (continuous_chartSection w) hz))
  have hSmooth := ((mem_principalSeries_iff ℂ n (complexPositionCharacter ds) F.val).mp F.2).1
  have hf : ContDiff ℝ ∞ f := by
    have hEq : (Langlands.Archimedean.unitsExtension F.val) ∘ (fun z => (chartSection w z).val) = f :=
      funext fun z => unitsExtension_val F.val (chartSection w z)
    rw [← hEq]
    exact (contDiffOn_unitsExtension hSmooth).comp_contDiff (contDiff_chartSection_val w)
      (fun z => (chartSection w z).isUnit)
  let φ : ChartTest n := ⟨f, hf, hS.of_isClosed_subset (isClosed_tsupport _) hSupp, subset_univ _⟩
  refine ⟨φ, hSupp, Subtype.ext (funext fun g => ?_)⟩
  by_cases hg : g ∈ chartDomain w
  · rw [extendTest_apply, extendTestMatrix_of_mem w ds φ hg, standard_chart_covariance w F hg]
    rfl
  · have hSg : g ∉ chartSaturation w S := fun h => hg ((mem_chartSaturation w S g).mp h).1
    exact (image_eq_zero_of_notMem_tsupport (fun h => hSg
      (chartSaturation_mono w hSupp (tsupport_extendTest_subset w ds φ h)))).trans
        (image_eq_zero_of_notMem_tsupport (fun h => hSg (hF h))).symm

/-- Compact Gauss cutoffs and recovery of sections from compact chart tests. -/
def ComplexBruhatCutoffStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (w : Equiv.Perm (Fin n))
    (O : Set (Coordinates n)) (g : G n),
    IsOpen O → g ∈ chartSaturation w O → ∃ η : ChartTest n,
      tsupport η ⊆ O ∧ chartCutoff w η =ᶠ[𝓝 g] 1 ∧
      ∀ F : SmoothStandard n ds, ∃ φ : ChartTest n, tsupport φ ⊆ tsupport η ∧
        extendTest w ds φ = cutoffSection w η F

theorem complexBruhatCutoff : ComplexBruhatCutoffStatement := by
  intro n ds w O g hO hg
  obtain ⟨η, hη, hEq⟩ := exists_chartCutoff w hO hg
  exact ⟨η, hη, hEq, fun F => exists_chartTest_of_tsupport w η.hasCompactSupport (cutoffSection w η F)
    (tsupport_cutoffSection_subset w η F)⟩

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatCutoff
