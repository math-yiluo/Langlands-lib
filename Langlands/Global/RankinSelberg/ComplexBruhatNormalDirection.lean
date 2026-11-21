import Langlands.Global.RankinSelberg.ComplexBruhatStabilizer
import Langlands.Analysis.MixedParameterDerivatives
import Langlands.HarmonicAnalysis.Distribution.ProductJetTransform

/-! # The induced normal derivative of a complex Bruhat stabilizer -/

noncomputable section

open Filter Set
open scoped Classical ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatNormalDirection

open Langlands.GeneralLinear (upperTriangularSubgroup upperBruhatCell mem_upperBruhatCell_mul)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.HarmonicAnalysis (productNormalDerivative productNormalDerivative_apply)
open Langlands.Analysis (fderiv_snd_slice_apply)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatGaussChart (chartSection chartCoordinates chartDomain chart_recover cellCoordinates
  isOpen_chartMatrixDomain contDiffOn_chartCoordinates complexBruhatGaussChart)
open ComplexBruhatTestExtension (chartUnitMatrixDomain isOpen_chartUnitMatrixDomain contDiffOn_chartMultiplier
  inducingMultiplier chartUpperMatrix)
open ComplexBruhatChartDerivative (chartVector chartScalar contDiff_chartSection_val contDiff_chartVector)
open ComplexBruhatLinearization (eventually_upper_line)
open ComplexBruhatStabilizer (TangentCoordinates NormalCoordinates splitCoordinates cellPoint cellPoint_mem
  mem_cellCoordinates_iff_snd_eq_zero complexBruhatStabilizer)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "B" => fun n => Langlands.GeneralLinear.upperTriangularSubgroup n ℂ
variable {n : ℕ}

private theorem chartSection_domain (w : Equiv.Perm (Fin n)) (z : Coordinates n) :
    chartSection w z ∈ chartDomain w ∧ chartCoordinates w (chartSection w z).val = z := by
  obtain ⟨hg, hz, _⟩ := chart_recover w (1 : B n) z
  simp only [Subgroup.coe_one, one_mul] at hg hz
  exact ⟨hg, hz⟩

private def normalProjection (w : Equiv.Perm (Fin n)) : Coordinates n →L[ℝ] NormalCoordinates w :=
  (ContinuousLinearMap.snd ℝ (TangentCoordinates w) (NormalCoordinates w)).comp
    (splitCoordinates w).toContinuousLinearMap

private theorem chartVector_tangent (w : Equiv.Perm (Fin n)) (X : Mat n) (hX : X.IsUpperTriangular)
    (z : Coordinates n) (hz : z ∈ cellCoordinates w) :
    normalProjection w (chartVector w X z) = 0 := by
  let g := chartSection w z
  let C := chartCoordinates w
  let D := normalProjection w
  have hg := chartSection_domain w z
  have hBruhat := (complexBruhatGaussChart n w).2.2
  have hCell : g ∈ upperBruhatCell n ℂ w := (hBruhat g).mpr ⟨hg.1, hg.2 ▸ hz⟩
  have hEq : (fun t : ℝ => D (C (g.val * (1 + t • X)))) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [eventually_upper_line X hX] with t ht
    obtain ⟨b, hb⟩ := ht
    have h := (hBruhat (g * b.val)).mp (mem_upperBruhatCell_mul n ℂ w b hCell)
    rw [← hb]
    exact (mem_cellCoordinates_iff_snd_eq_zero w _).mp h.2
  have hp : HasDerivAt (fun t : ℝ => g.val * (1 + t • X)) (g.val * X) 0 := by
    simpa only [mul_add, mul_one, Matrix.mul_smul, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (g.val * X)).const_add g.val
  have hC : DifferentiableAt ℝ C g.val := ((contDiffOn_chartCoordinates w).contDiffAt
    ((isOpen_chartMatrixDomain w).mem_nhds hg.1)).differentiableAt (by simp)
  have hh := ((D.hasFDerivAt.comp g.val hC.hasFDerivAt).comp_hasDerivAt_of_eq 0 hp (by simp)).deriv
  change deriv (fun t : ℝ => D (C (g.val * (1 + t • X)))) 0 = D (chartVector w X z) at hh
  rw [hEq.deriv_eq, deriv_const] at hh
  exact hh.symm

private theorem chartVector_derivative_tangent (w : Equiv.Perm (Fin n)) (X : Mat n)
    (hX : X.IsUpperTriangular) {z : Coordinates n} (hz : z ∈ cellCoordinates w)
    (v : Coordinates n) (hv : v ∈ cellCoordinates w) :
    normalProjection w (fderiv ℝ (chartVector w X) z v) = 0 := by
  let D := normalProjection w
  have hz' : D z = 0 := (mem_cellCoordinates_iff_snd_eq_zero w z).mp hz
  have hv' : D v = 0 := (mem_cellCoordinates_iff_snd_eq_zero w v).mp hv
  have h0 (t : ℝ) : z + t • v ∈ cellCoordinates w := by
    apply (mem_cellCoordinates_iff_snd_eq_zero w _).mpr
    change D (z + t • v) = 0
    rw [map_add, map_smul, hz', hv', smul_zero, add_zero]
  have hzero : (fun t : ℝ => D (chartVector w X (z + t • v))) = 0 :=
    funext fun t => chartVector_tangent w X hX _ (h0 t)
  have hp : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hC := (contDiff_chartVector w X).differentiable (by simp) z
  have hh := ((D.hasFDerivAt.comp z hC.hasFDerivAt).comp_hasDerivAt_of_eq 0 hp (by simp)).deriv
  change deriv (fun t : ℝ => D (chartVector w X (z + t • v))) 0 = D (fderiv ℝ (chartVector w X) z v) at hh
  rw [hzero, deriv_zero] at hh
  exact hh.symm

private theorem contDiff_varying_chart_differential {P A : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup A] [NormedSpace ℝ A]
    (w : Equiv.Perm (Fin n)) {f : Mat n → A} (hf : ContDiffOn ℝ ∞ f (chartUnitMatrixDomain w))
    {z : P → Coordinates n} {X : P → Mat n} (hz : ContDiff ℝ ∞ z) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ f (chartSection w (z p)).val ((chartSection w (z p)).val * X p)) := by
  have hSec := (contDiff_chartSection_val w).comp hz
  have hDer : ContDiff ℝ ∞ (fun p => fderiv ℝ f (chartSection w (z p)).val) := by
    apply contDiffOn_univ.mp
    exact (hf.fderiv_of_isOpen (isOpen_chartUnitMatrixDomain w) (by simp)).comp hSec.contDiffOn
      (fun p _ => ⟨(chartSection w (z p)).isUnit, (chartSection_domain w (z p)).1⟩)
  exact hDer.clm_apply (hSec.mul hX)

theorem contDiff_varying_chartScalar {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData) {z : P → Coordinates n} {X : P → Mat n}
    (hz : ContDiff ℝ ∞ z) (hX : ContDiff ℝ ∞ X) : ContDiff ℝ ∞ (fun p => chartScalar w ds (X p) (z p)) :=
  contDiff_varying_chart_differential w (contDiffOn_chartMultiplier w ds) hz hX

/-- The chart field of the stabilizing family in the split tangential and normal coordinates. -/
def splitChartVector (w : Equiv.Perm (Fin n)) (X : TangentCoordinates w → Mat n)
    (p : TangentCoordinates w × NormalCoordinates w) : TangentCoordinates w × NormalCoordinates w :=
  splitCoordinates w (chartVector w (X p.1) ((splitCoordinates w).symm p))

theorem contDiff_splitChartVector (w : Equiv.Perm (Fin n)) {X : TangentCoordinates w → Mat n}
    (hX : ContDiff ℝ ∞ X) : ContDiff ℝ ∞ (splitChartVector w X) :=
  (splitCoordinates w).contDiff.comp (contDiff_varying_chart_differential w
    ((contDiffOn_chartCoordinates w).mono inter_subset_right) (splitCoordinates w).symm.contDiff
    (hX.comp contDiff_fst))

set_option maxHeartbeats 850000 in
private theorem splitChartVector_normal_cube (w : Equiv.Perm (Fin n))
    {X : TangentCoordinates w → Mat n} (hX : ContDiff ℝ ∞ X) (x : TangentCoordinates w)
    (hU : (X x).IsUpperTriangular) (hCube : fderiv ℝ (chartVector w (X x)) (cellPoint w x) ^ 3 = 0) :
    productNormalDerivative (splitChartVector w X) x ^ 3 = 0 := by
  let e := splitCoordinates w
  let D := fderiv ℝ (chartVector w (X x)) (cellPoint w x)
  let M := e.toContinuousLinearMap.comp (D.comp e.symm.toContinuousLinearMap)
  let N := productNormalDerivative (splitChartVector w X) x
  let F : TangentCoordinates w × NormalCoordinates w → TangentCoordinates w × NormalCoordinates w :=
    fun p => e (chartVector w (X x) (e.symm p))
  have hF : ContDiff ℝ ∞ F := e.contDiff.comp ((contDiff_chartVector w (X x)).comp e.symm.contDiff)
  have hD (v : TangentCoordinates w × NormalCoordinates w) :
      fderiv ℝ F (x, 0) v = M v := by
    have hV := (contDiff_chartVector w (X x)).differentiable (by simp) (e.symm (x, 0))
    have hD' := (e.toContinuousLinearMap.hasFDerivAt.comp (x, 0)
      (hV.hasFDerivAt.comp (x, 0) e.symm.toContinuousLinearMap.hasFDerivAt)).fderiv
    exact DFunLike.congr_fun hD' v
  have hN (y : NormalCoordinates w) : N y = (M (0, y)).2 := by
    rw [show N y = (fderiv ℝ (splitChartVector w X) (x, 0) (0, y)).2 from rfl,
      ← fderiv_snd_slice_apply ((contDiff_splitChartVector w hX).differentiable (by simp) (x, 0)) y,
      show (fun y => splitChartVector w X (x, y)) = fun y => F (x, y) from rfl,
      fderiv_snd_slice_apply (hF.differentiable (by simp) (x, 0)) y, hD]
  have hTan (t : TangentCoordinates w) : (M (t, 0)).2 = 0 :=
    chartVector_derivative_tangent w (X x) hU (cellPoint_mem w x) (cellPoint w t) (cellPoint_mem w t)
  have hComm (p : TangentCoordinates w × NormalCoordinates w) : N p.2 = (M p).2 := by
    nth_rw 2 [show p = (p.1, 0) + (0, p.2) by simp]
    rw [map_add, Prod.snd_add, hTan, zero_add, hN]
  have hM (p : TangentCoordinates w × NormalCoordinates w) : M (M (M p)) = 0 := by
    change e (D (e.symm (e (D (e.symm (e (D (e.symm p)))))))) = 0
    simp only [e.symm_apply_apply]
    rw [show D (D (D (e.symm p))) = (D ^ 3) (e.symm p) from rfl, hCube, zero_apply, map_zero]
  apply ContinuousLinearMap.ext
  intro y
  change N (N (N y)) = 0
  rw [hN y, hComm, hComm, hM]
  rfl

/-- The smooth stabilizing family can be used as a vector field in the split chart.
Its normal derivative has cube zero along the cell. -/
def ComplexBruhatNormalDirectionStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (w : Equiv.Perm (Fin (r + 1))),
    (¬ StrictAnti w) →
    ∃ X : TangentCoordinates w → Mat (r + 1), ContDiff ℝ ∞ X ∧
      ContDiff ℝ ∞ (splitChartVector w X) ∧
      ∀ x : TangentCoordinates w,
        (∀ p q, q ≤ p → X x p q = 0) ∧
        complexWhittakerFrequency a (X x) = ((4 * Real.pi : ℝ) : ℂ) * Complex.I ∧
        splitChartVector w X (x, 0) = 0 ∧ chartScalar w ds (X x) (cellPoint w x) = 0 ∧
        productNormalDerivative (splitChartVector w X) x ^ 3 = 0

theorem complexBruhatNormalDirection : ComplexBruhatNormalDirectionStatement := by
  intro r ds a w hw
  obtain ⟨X, hSmooth, h⟩ := complexBruhatStabilizer r ds a w hw
  refine ⟨X, hSmooth, contDiff_splitChartVector w hSmooth, fun x => ?_⟩
  obtain ⟨hU, hFreq, hVec, hScalar, hCube⟩ := h x
  refine ⟨hU, hFreq, ?_, hScalar, splitChartVector_normal_cube w hSmooth x (fun i j hij => hU i j hij.le) hCube⟩
  change splitCoordinates w (chartVector w (X x) (cellPoint w x)) = 0
  rw [hVec, map_zero]

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatNormalDirection
