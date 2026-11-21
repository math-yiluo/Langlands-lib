import Langlands.Global.RankinSelberg.ComplexBruhatChartDistribution
import Langlands.Global.RankinSelberg.ComplexSmoothWhittakerDerivative

/-! # Right differentiation in the complex Bruhat test charts -/

noncomputable section

open Set Filter TopologicalSpace
open scoped Classical ContDiff Distributions Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatChartDerivative

open Langlands.Archimedean (complexPositionCharacter mem_principalSeries_iff principalSeriesCharacter_eq
  principalSeriesCharacter borelChar borelFactor borelFactor_eq_unitChar posWeight posExponent
  unitsExtension unitsExtension_val rightDerivative_eq_fderiv)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.GeneralLinear (upperTriangularSubgroup diagonalUnits_mem_upperTriangular)
open Langlands.GeneralLinear.UpperBruhatCoordinates (diagUnit)
open ComplexOppositeCompactChart (Coordinates oppositePoint contDiff_oppositePoint_val)
open ComplexBruhatGaussChart (chartDomain chartCoordinates chartMatrixDomain chartUpper chartSection
  chart_recover chart_factorization chartUpper_mem contDiffOn_chartCoordinates)
open ComplexBruhatTestExtension (ChartTest chartUnitMatrixDomain isOpen_chartUnitMatrixDomain
  chartUpperMatrix chartUpperMatrix_val inducingMultiplier inducingMultiplier_one contDiffOn_chartMultiplier
  extendTest extendTest_apply extendTestMatrix extendTestMatrix_of_mem extendTestMatrix_zero extendTest_chartSection
  chartSaturation mem_chartSaturation isClosed_chartSaturation tsupport_extendTest_subset)
open ComplexWhittakerSmoothExtension (SmoothStandard compactProfile)
open ComplexWhittakerTranslateExtension (smoothTranslate)
open ComplexSmoothWhittakerDerivative (smoothDerivative smoothDerivative_apply complexSmoothWhittakerDerivative)
open ComplexCompactSmoothDifferences (CompactProfileDifferenceBound)
open ComplexBruhatChartDistribution (complexBruhatChartDistribution)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "B" => fun n => Langlands.GeneralLinear.upperTriangularSubgroup n ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ

variable {n : ℕ} {ds : List ComplexCharacterData}

/-- The defining diagonal and unipotent covariance gives covariance under the whole Borel. -/
theorem standard_borel_covariance (F : SmoothStandard n ds) (b : B n) (g : G n) :
    F.val (b.val * g) = inducingMultiplier ds b.val.val * F.val g := by
  let a := diagUnit b
  let d := Langlands.GeneralLinear.Iwasawa.diagonalUnits a
  have hd : d⁻¹ = Langlands.GeneralLinear.Iwasawa.diagonalUnits a⁻¹ := (map_inv Langlands.GeneralLinear.Iwasawa.diagonalUnits a).symm
  have hu : d⁻¹ * b.val ∈ B n := mul_mem
    (inv_mem (diagonalUnits_mem_upperTriangular n a)) b.2
  have hud (i : Fin n) : (d⁻¹ * b.val).val i i = 1 := by
    rw [Units.val_mul, hd, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.diagonal_mul]
    change ((a i)⁻¹ : ℂˣ).val * b.val.val i i = 1
    have he : (a i : ℂ) = b.val.val i i := rfl
    rw [← he]
    exact (a i).inv_val
  let u : N n := ⟨d⁻¹ * b.val, hu, hud⟩
  have hdu : d * u.val = b.val := mul_inv_cancel_left _ _
  have hχ : inducingMultiplier ds b.val.val = principalSeriesCharacter ℂ n (complexPositionCharacter ds) a := by
    change (∏ i : Fin n, borelFactor (posWeight ds i)
      (2 * (posExponent ds i + (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)))) (a i)) = _
    rw [principalSeriesCharacter_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [borelFactor_eq_unitChar, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)]
  rw [hχ, ← hdu]
  exact ((mem_principalSeries_iff ℂ n (complexPositionCharacter ds) F.val).mp F.2).2 a u g

theorem standard_chart_covariance (w : Equiv.Perm (Fin n)) (F : SmoothStandard n ds)
    {g : G n} (hg : g ∈ chartDomain w) :
    F.val g = inducingMultiplier ds (chartUpper w g).val * F.val (chartSection w (chartCoordinates w g.val)) := by
  let b : B n := ⟨chartUpper w g, chartUpper_mem w g hg⟩
  let z := chartSection w (chartCoordinates w g.val)
  calc
    F.val g = F.val (b.val * z) := congrArg F.val (chart_factorization w g).symm
    _ = inducingMultiplier ds b.val.val * F.val z := standard_borel_covariance F b z

theorem contDiff_chartSection_val (w : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ (fun z => (chartSection w z).val) := by
  have hInv : ContDiff ℝ ∞ (fun z : Coordinates n => ((oppositePoint z)⁻¹ : G n).val) := by
    simp_rw [← Ring.inverse_unit]
    refine contDiff_iff_contDiffAt.mpr fun z => ?_
    have h : ContDiffAt ℝ ∞ (Ring.inverse : Mat n → Mat n) (oppositePoint z).val :=
      contDiffAt_ringInverse ℝ (oppositePoint z)
    exact h.comp z (contDiff_oppositePoint_val n).contDiffAt
  exact hInv.mul contDiff_const

private theorem chartSection_factors (w : Equiv.Perm (Fin n)) (z : Coordinates n) :
    (chartSection w z).val ∈ chartUnitMatrixDomain w ∧
      chartCoordinates w (chartSection w z).val = z ∧ chartUpper w (chartSection w z) = 1 := by
  obtain ⟨hD, hC, hB⟩ := chart_recover w (1 : B n) z
  simp only [Subgroup.coe_one, one_mul] at hD hC hB
  exact ⟨⟨(chartSection w z).isUnit, hD⟩, hC, hB⟩

/-- The infinitesimal right action on the lower coordinates of the chart. -/
def chartVector (w : Equiv.Perm (Fin n)) (X : Mat n) (z : Coordinates n) : Coordinates n :=
  fderiv ℝ (chartCoordinates w) (chartSection w z).val ((chartSection w z).val * X)

/-- The infinitesimal right action on the normalized inducing multiplier. -/
def chartScalar (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData) (X : Mat n) (z : Coordinates n) : ℂ :=
  fderiv ℝ (fun A => inducingMultiplier ds (chartUpperMatrix w A)) (chartSection w z).val
    ((chartSection w z).val * X)

private theorem contDiff_chart_directional {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (w : Equiv.Perm (Fin n)) (X : Mat n) {f : Mat n → A}
    (hf : ContDiffOn ℝ ∞ f (chartUnitMatrixDomain w)) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ f (chartSection w z).val ((chartSection w z).val * X)) := by
  have hS := contDiff_chartSection_val w
  have hDF : ContDiff ℝ ∞ (fun z => fderiv ℝ f (chartSection w z).val) := by
    apply contDiffOn_univ.mp
    exact (hf.fderiv_of_isOpen (isOpen_chartUnitMatrixDomain w) (by simp)).comp hS.contDiffOn
      (fun z _ => (chartSection_factors w z).1)
  exact hDF.clm_apply (hS.mul contDiff_const)

theorem contDiff_chartVector (w : Equiv.Perm (Fin n)) (X : Mat n) : ContDiff ℝ ∞ (chartVector w X) :=
  contDiff_chart_directional w X ((contDiffOn_chartCoordinates w).mono inter_subset_right)

theorem contDiff_chartScalar (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData) (X : Mat n) :
    ContDiff ℝ ∞ (chartScalar w ds X) := contDiff_chart_directional w X (contDiffOn_chartMultiplier w ds)

/-- The first-order operator on a test in the Gauss chart. -/
def chartDerivativeTest (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData) (X : Mat n)
    (φ : ChartTest n) : ChartTest n := by
  let f (z : Coordinates n) := fderiv ℝ φ z (chartVector w X z) + chartScalar w ds X z * φ z
  have hs : Function.support f ⊆ tsupport φ := by
    intro z hz
    by_contra hφ
    exact hz (by simp [f, fderiv_of_notMem_tsupport ℝ hφ, image_eq_zero_of_notMem_tsupport hφ])
  exact ⟨f, ((φ.contDiff.fderiv_right (by simp)).clm_apply (contDiff_chartVector w X)).add
    ((contDiff_chartScalar w ds X).mul φ.contDiff),
    HasCompactSupport.of_support_subset_isCompact φ.hasCompactSupport hs, le_top⟩

@[simp] theorem chartDerivativeTest_apply (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (X : Mat n) (φ : ChartTest n) (z : Coordinates n) :
    chartDerivativeTest w ds X φ z = fderiv ℝ φ z (chartVector w X z) + chartScalar w ds X z * φ z := rfl

theorem tsupport_chartDerivativeTest_subset (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (X : Mat n) (φ : ChartTest n) : tsupport (chartDerivativeTest w ds X φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro z hz
  by_contra hφ
  exact hz (by simp [fderiv_of_notMem_tsupport ℝ hφ, image_eq_zero_of_notMem_tsupport hφ])

private theorem smoothDerivative_extendTest_at_section (w : Equiv.Perm (Fin n)) (X : Mat n)
    (φ : ChartTest n) (z : Coordinates n) :
    (smoothDerivative X (extendTest w ds φ)).val (chartSection w z) = chartDerivativeTest w ds X φ z := by
  let F := extendTest w ds φ
  let g := chartSection w z
  let m := fun A => inducingMultiplier ds (chartUpperMatrix w A)
  let f := fun A => m A * φ (chartCoordinates w A)
  obtain ⟨hg, hC, hB⟩ := chartSection_factors w z
  have hEq : unitsExtension F.val =ᶠ[𝓝 g.val] f := by
    filter_upwards [(isOpen_chartUnitMatrixDomain w).mem_nhds hg] with A hA
    let y : G n := hA.1.unit
    have hy : y.val = A := hA.1.unit_spec
    have hc : y ∈ chartDomain w := show y.val ∈ chartMatrixDomain w from hy.symm ▸ hA.2
    rw [← hy, unitsExtension_val]
    change extendTestMatrix w ds φ y.val = _
    rw [extendTestMatrix_of_mem w ds φ hc, ← chartUpperMatrix_val]
  have hdM : DifferentiableAt ℝ m g.val :=
    ((contDiffOn_chartMultiplier w ds).contDiffAt ((isOpen_chartUnitMatrixDomain w).mem_nhds hg)).differentiableAt (by simp)
  have hdC : DifferentiableAt ℝ (chartCoordinates w) g.val :=
    (((contDiffOn_chartCoordinates w).mono (show chartUnitMatrixDomain w ⊆ chartMatrixDomain w from inter_subset_right)).contDiffAt
      ((isOpen_chartUnitMatrixDomain w).mem_nhds hg)).differentiableAt (by simp)
  have hφ := φ.contDiff.differentiable (by simp) (chartCoordinates w g.val)
  have hm : m g.val = 1 := by
    change inducingMultiplier ds (chartUpperMatrix w (chartSection w z).val) = 1
    rw [chartUpperMatrix_val, hB, Units.val_one, inducingMultiplier_one]
  change (smoothDerivative X F).val g = _
  rw [smoothDerivative_apply, rightDerivative_eq_fderiv F.2.1, hEq.fderiv_eq]
  change fderiv ℝ (fun A => m A * (⇑φ ∘ chartCoordinates w) A) g.val (g.val * X) = _
  rw [fderiv_fun_mul hdM (hφ.comp g.val hdC), fderiv_comp g.val hφ hdC, chartDerivativeTest_apply]
  simp only [hm, one_smul, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply, smul_eq_mul]
  rw [show chartCoordinates w g.val = z from hC, mul_comm (φ z)]
  rfl

private theorem smoothDerivative_extendTest_off_chart (w : Equiv.Perm (Fin n)) (X : Mat n)
    (φ : ChartTest n) {g : G n} (hg : g ∉ chartDomain w) :
    (smoothDerivative X (extendTest w ds φ)).val g = 0 := by
  let F := extendTest w ds φ
  let U := (chartSaturation w (tsupport φ))ᶜ
  have hU : IsOpen (Units.val '' U) := Units.isOpenEmbedding_val.isOpenMap _
    (isClosed_chartSaturation w φ.hasCompactSupport).isOpen_compl
  have hUg : g.val ∈ Units.val '' U := ⟨g, fun h => hg ((mem_chartSaturation w _ g).mp h).1, rfl⟩
  have he : unitsExtension F.val =ᶠ[𝓝 g.val] (fun _ => (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hUg] with A hA
    obtain ⟨y, hy, rfl⟩ := hA
    rw [unitsExtension_val]
    exact extendTestMatrix_zero w ds φ hy
  rw [smoothDerivative_apply, rightDerivative_eq_fderiv F.2.1, he.fderiv_eq]
  simp

/-- Right differentiation of an extended chart test is the extension of its chart derivative. -/
theorem smoothDerivative_extendTest (w : Equiv.Perm (Fin n)) (X : Mat n) (φ : ChartTest n) :
    smoothDerivative X (extendTest w ds φ) = extendTest w ds (chartDerivativeTest w ds X φ) := by
  apply Subtype.ext
  funext g
  change (smoothDerivative X (extendTest w ds φ)).val g = (extendTest w ds (chartDerivativeTest w ds X φ)).val g
  by_cases hg : g ∈ chartDomain w
  · rw [standard_chart_covariance w (smoothDerivative X (extendTest w ds φ)) hg,
      standard_chart_covariance w (extendTest w ds (chartDerivativeTest w ds X φ)) hg,
      smoothDerivative_extendTest_at_section, extendTest_chartSection]
  · rw [smoothDerivative_extendTest_off_chart w X φ hg, extendTest_apply]
    exact (extendTestMatrix_zero w ds _ (fun h => hg ((mem_chartSaturation w _ g).mp h).1)).symm

/-- An exact smooth Whittaker functional has the chart distribution equation for
all strictly upper directions. -/
def ComplexBruhatChartDerivativeStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (w : Equiv.Perm (Fin (r + 1)))
    (L : SmoothStandard (r + 1) ds →ₗ[ℂ] ℂ) (J : ℕ) (C : ℝ), 0 ≤ C →
    (∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R) →
    (∀ F (u : G (r + 1)), u ∈ N (r + 1) → L (smoothTranslate u F) = complexWhittakerCharacter a u * L F) →
    ∃ T : ChartTest (r + 1) →L[ℂ] ℂ,
      (∀ φ : ChartTest (r + 1), T φ = L (extendTest w ds φ)) ∧
      ∀ (X : Mat (r + 1)), (∀ i j, j ≤ i → X i j = 0) → ∀ φ : ChartTest (r + 1),
        T (chartDerivativeTest w ds X φ) = complexWhittakerFrequency a X * T φ

theorem complexBruhatChartDerivative : ComplexBruhatChartDerivativeStatement := by
  intro r ds a w L J C hC hL hCov
  obtain ⟨T, hT⟩ := complexBruhatChartDistribution (r + 1) ds w L J C hC hL
  refine ⟨T, hT, fun X hX φ => ?_⟩
  rw [hT, hT, ← smoothDerivative_extendTest]
  exact complexSmoothWhittakerDerivative r ds a L J C hL hCov (extendTest w ds φ) X hX

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatChartDerivative
