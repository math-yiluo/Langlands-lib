import Langlands.Global.RankinSelberg.ComplexBruhatChartDerivative
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonReflectedHaar

/-! # The actual upper-unipotent group in the long complex Gauss chart -/

noncomputable section

open Set TopologicalSpace
open scoped Classical ContDiff Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexOpenBruhatCoordinates

open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter_apply)
open Langlands.GeneralLinear (weylLong weylLong_inv weylLong_mul_self upperEntryCoordinates
  upperEntryCoordinates_mul upperEntryCoordinates_apply upperBruhatCell mem_upperBruhatCell_mul
  upperUnipotent_le_upperTriangular inverseTranspose inverseTranspose_coe inverseTranspose_involutive
  inverseTranspose_weylLong)
open Langlands.RankinSelberg (reflectedUnipotentEquiv reflectedUnipotent_involutive)
open Langlands.Whittaker (reflectedUnipotent reflectedUnipotent_val)
open ComplexOppositeCompactChart (Coordinates oppositePoint oppositePoint_upperEntries contDiff_oppositePoint_val)
open ComplexModulusOpenCell (groupTranspose groupTranspose_val)
open ComplexBruhatGaussChart (chartDomain chartCoordinates chartSection chartUpper chartUpper_mem
  chart_factorization cellCoordinates allowedLowerEntry complexBruhatGaussChart)
open ComplexBruhatTestExtension (ChartTest extendTest extendTest_apply extendTest_chartSection
  extendTestMatrix_zero mem_chartSaturation)
open ComplexBruhatChartDerivative (standard_borel_covariance)
open ComplexWhittakerTranslateExtension (smoothTranslate smoothTranslate_apply)

local notation "Mat" => fun n => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
local notation "G" => fun n => Langlands.GeneralLinear (n + 1) ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent (n + 1) ℂ

variable {r : ℕ}

/-- Coordinates in which the Gauss representative is the long Weyl matrix times the
actual upper-unipotent element. -/
def openCoordinates (r : ℕ) : N r ≃ₜ Coordinates (r + 1) :=
  (reflectedUnipotentEquiv (K := ℂ) r).toHomeomorph.trans (upperEntryCoordinates (r + 1))

theorem chartSection_openCoordinates (u : N r) :
    chartSection Fin.revPerm (openCoordinates r u) = weylLong (r + 1) ℂ * u.val := by
  have hOpp : oppositePoint (openCoordinates r u) = weylLong (r + 1) ℂ * u.val⁻¹ * weylLong (r + 1) ℂ := by
    change oppositePoint (upperEntryCoordinates (r + 1) (reflectedUnipotent u)) = _
    rw [oppositePoint_upperEntries, reflectedUnipotent_val, groupTranspose]
    simp only [mul_inv_rev, map_mul, weylLong_inv, inverseTranspose_weylLong, map_inv,
      inverseTranspose_involutive, mul_assoc]
  change (oppositePoint (openCoordinates r u))⁻¹ * weylLong (r + 1) ℂ = _
  rw [hOpp]
  simp only [mul_inv_rev, weylLong_inv, inv_inv, mul_assoc, weylLong_mul_self, mul_one]

theorem chartDomain_long_eq_cell (r : ℕ) :
    chartDomain (Fin.revPerm : Equiv.Perm (Fin (r + 1))) = upperBruhatCell (r + 1) ℂ Fin.revPerm := by
  ext g
  rw [(complexBruhatGaussChart (r + 1) Fin.revPerm).2.2 g]
  refine (and_iff_left ?_).symm
  intro p hp
  exact (hp (by simpa only [allowedLowerEntry, Fin.revPerm_symm, Fin.revPerm_apply] using
    (Fin.rev_lt_rev.mpr p.2))).elim

private theorem reflected_openCoordinates_symm (r : ℕ) (z : Coordinates (r + 1)) :
    reflectedUnipotent ((openCoordinates r).symm z) = (upperEntryCoordinates (K := ℂ) (r + 1)).symm z := by
  apply (upperEntryCoordinates (K := ℂ) (r + 1)).injective
  exact ((openCoordinates r).apply_symm_apply z).trans
    (((upperEntryCoordinates (K := ℂ) (r + 1)).apply_symm_apply z).symm)

private theorem contDiff_upperPoint_val (r : ℕ) :
    ContDiff ℝ ∞ (fun z => ((upperEntryCoordinates (K := ℂ) (r + 1)).symm z).val.val) := by
  let tr : Mat r →L[ℝ] Mat r :=
    (Matrix.transposeLinearEquiv (Fin (r + 1)) (Fin (r + 1)) ℝ ℂ).toLinearMap.toContinuousLinearMap
  have he : (fun z => ((upperEntryCoordinates (K := ℂ) (r + 1)).symm z).val.val) =
      tr ∘ (fun z => (oppositePoint z).val) := by
    funext z
    change _ = (oppositePoint z).val.transpose
    rw [oppositePoint, groupTranspose_val, Matrix.transpose_transpose]
  rw [he]
  exact tr.contDiff.comp (contDiff_oppositePoint_val (r + 1))

private theorem contDiff_inverse_upperPoint_val (r : ℕ) :
    ContDiff ℝ ∞ (fun z => (((upperEntryCoordinates (K := ℂ) (r + 1)).symm z).val : G r)⁻¹.val) := by
  simp_rw [← Ring.inverse_unit]
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  exact (contDiffAt_ringInverse ℝ ((upperEntryCoordinates (K := ℂ) (r + 1)).symm z).val).comp z
    (contDiff_upperPoint_val r).contDiffAt

theorem contDiff_openCoordinates_symm_val (r : ℕ) :
    ContDiff ℝ ∞ (fun z => ((openCoordinates r).symm z).val.val) := by
  let tr : Mat r →L[ℝ] Mat r :=
    (Matrix.transposeLinearEquiv (Fin (r + 1)) (Fin (r + 1)) ℝ ℂ).toLinearMap.toContinuousLinearMap
  let w := (weylLong (r + 1) ℂ).val
  have he (z : Coordinates (r + 1)) : (openCoordinates r).symm z =
      reflectedUnipotent ((upperEntryCoordinates (K := ℂ) (r + 1)).symm z) := by
    rw [← reflected_openCoordinates_symm r z, reflectedUnipotent_involutive]
  simp_rw [he, reflectedUnipotent_val, Units.val_mul, inverseTranspose_coe]
  exact (contDiff_const (c := w)).mul
    (tr.contDiff.comp (contDiff_inverse_upperPoint_val r)) |>.mul (contDiff_const (c := w))

theorem contDiff_openCoordinates_mul (r : ℕ) :
    ContDiff ℝ ∞ (fun p : Coordinates (r + 1) × Coordinates (r + 1) =>
      openCoordinates r ((openCoordinates r).symm p.1 * (openCoordinates r).symm p.2)) := by
  let e := openCoordinates r
  let q := upperEntryCoordinates (K := ℂ) (r + 1)
  have he (p : Coordinates (r + 1) × Coordinates (r + 1)) :
      e (e.symm p.1 * e.symm p.2) = q (q.symm p.1 * q.symm p.2) := by
    change q (reflectedUnipotentEquiv (K := ℂ) r (e.symm p.1 * e.symm p.2)) = _
    rw [map_mul]
    exact congrArg₂ (fun u v : N r => q (u * v)) (reflected_openCoordinates_symm r p.1)
      (reflected_openCoordinates_symm r p.2)
  simp_rw [show openCoordinates r = e from rfl, he]
  apply contDiff_pi.mpr
  intro ij
  simp_rw [q, upperEntryCoordinates_mul, Homeomorph.apply_symm_apply]
  have hFst : ContDiff ℝ ∞ (Prod.fst : Coordinates (r + 1) × Coordinates (r + 1) → Coordinates (r + 1)) :=
    contDiff_fst
  have hSnd : ContDiff ℝ ∞ (Prod.snd : Coordinates (r + 1) × Coordinates (r + 1) → Coordinates (r + 1)) :=
    contDiff_snd
  exact ((contDiff_pi.mp hFst ij).add (contDiff_pi.mp hSnd ij)).add
    (ContDiff.sum (fun k _ => (contDiff_pi.mp hFst ⟨(ij.val.1, k.val), k.2.1⟩).mul
      (contDiff_pi.mp hSnd ⟨(k.val, ij.val.2), k.2.2⟩)))

theorem contDiff_openCoordinates_inv (r : ℕ) :
    ContDiff ℝ ∞ (fun z : Coordinates (r + 1) => openCoordinates r ((openCoordinates r).symm z)⁻¹) := by
  let q := upperEntryCoordinates (K := ℂ) (r + 1)
  have he (z : Coordinates (r + 1)) : openCoordinates r ((openCoordinates r).symm z)⁻¹ =
      q (q.symm z)⁻¹ := by
    change q (reflectedUnipotentEquiv (K := ℂ) r ((openCoordinates r).symm z)⁻¹) = _
    rw [map_inv]
    exact congrArg (fun u : N r => q u⁻¹) (reflected_openCoordinates_symm r z)
  simp_rw [he]
  apply contDiff_pi.mpr
  intro ij
  simp_rw [q, upperEntryCoordinates_apply]
  exact ((Matrix.entryLinearMap ℝ ℂ ij.val.1 ij.val.2).toContinuousLinearMap.contDiff).comp
    (contDiff_inverse_upperPoint_val r)

/-- The test extension commutes with the right unipotent action on the long chart. -/
theorem smoothTranslate_extendTest_long (ds : List ComplexCharacterData) (u : N r)
    (φ φ' : ChartTest (r + 1))
    (hφ' : ∀ z, φ' z = φ (openCoordinates r ((openCoordinates r).symm z * u))) :
    extendTest Fin.revPerm ds φ' = smoothTranslate u.val (extendTest Fin.revPerm ds φ) := by
  let e := openCoordinates r
  let w : Equiv.Perm (Fin (r + 1)) := Fin.revPerm
  have he (z : Coordinates (r + 1)) : chartSection w z * u.val = chartSection w (e (e.symm z * u)) := by
    have h := chartSection_openCoordinates (e.symm z)
    rw [e.apply_symm_apply] at h
    rw [h, chartSection_openCoordinates (e.symm z * u), Subgroup.coe_mul, mul_assoc]
  apply Subtype.ext
  funext g
  change (extendTest w ds φ').val g = (extendTest w ds φ).val (g * u.val)
  by_cases hg : g ∈ chartDomain w
  · let z := chartCoordinates w g.val
    let b : Langlands.GeneralLinear.upperTriangularSubgroup (r + 1) ℂ :=
      ⟨chartUpper w g, chartUpper_mem w g hg⟩
    have h := chart_factorization w g
    change b.val * chartSection w z = g at h
    have hgu : g * u.val = b.val * chartSection w (e (e.symm z * u)) := by
      rw [← he, ← mul_assoc, h]
    rw [← h, standard_borel_covariance, extendTest_chartSection, hφ']
    rw [h, hgu, standard_borel_covariance, extendTest_chartSection]
  · have hgu : g * u.val ∉ chartDomain w := by
      intro hgu
      rw [chartDomain_long_eq_cell] at hg hgu
      let b : Langlands.GeneralLinear.upperTriangularSubgroup (r + 1) ℂ :=
        ⟨u.val, upperUnipotent_le_upperTriangular (r + 1) ℂ u.2⟩
      apply hg
      have h := mem_upperBruhatCell_mul (r + 1) ℂ w b⁻¹ hgu
      change (g * u.val) * u.val⁻¹ ∈ upperBruhatCell (r + 1) ℂ w at h
      simpa only [mul_inv_cancel_right] using h
    rw [extendTest_apply, extendTest_apply, extendTestMatrix_zero w ds φ' (fun h => hg ((mem_chartSaturation w _ _).mp h).1),
      extendTestMatrix_zero w ds φ (fun h => hgu ((mem_chartSaturation w _ _).mp h).1)]

/-- The standard Whittaker character is smooth in the open Bruhat coordinates. -/
theorem contDiff_openWhittakerCharacter (a : ℂˣ) :
    ContDiff ℝ ∞ (fun z => complexWhittakerCharacter a ((openCoordinates r).symm z).val) := by
  have hSum : ContDiff ℝ ∞ (fun z : Coordinates (r + 1) =>
      ∑ i : Fin r, ((openCoordinates r).symm z).val.val i.castSucc i.succ) :=
    ContDiff.sum (fun i _ =>
      (Matrix.entryLinearMap ℝ ℂ i.castSucc i.succ).toContinuousLinearMap.contDiff.comp
        (contDiff_openCoordinates_symm_val r))
  have hTrace : ContDiff ℝ ∞ (fun x : ℂ => Algebra.trace ℝ ℂ x) :=
    (Algebra.trace ℝ ℂ).toContinuousLinearMap.contDiff
  simp only [complexWhittakerCharacter, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    complexScaledCharacter_apply, Real.fourierChar_apply]
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
    (hTrace.comp (contDiff_const.mul hSum)))).mul contDiff_const).cexp

/-- The long Gauss representatives carry the actual unipotent group, its smooth
coordinate laws, and its smooth Whittaker character. -/
def ComplexOpenBruhatCoordinatesStatement : Prop :=
  ∀ r : ℕ, (∀ u : N r, chartSection Fin.revPerm (openCoordinates r u) = weylLong (r + 1) ℂ * u.val) ∧
    ContDiff ℝ ∞ (fun p : Coordinates (r + 1) × Coordinates (r + 1) =>
      openCoordinates r ((openCoordinates r).symm p.1 * (openCoordinates r).symm p.2)) ∧
    ContDiff ℝ ∞ (fun z : Coordinates (r + 1) => openCoordinates r ((openCoordinates r).symm z)⁻¹) ∧
    ∀ a : ℂˣ, ContDiff ℝ ∞ (fun z => complexWhittakerCharacter a ((openCoordinates r).symm z).val)

theorem complexOpenBruhatCoordinates : ComplexOpenBruhatCoordinatesStatement :=
  fun r => ⟨chartSection_openCoordinates, contDiff_openCoordinates_mul r, contDiff_openCoordinates_inv r,
    contDiff_openWhittakerCharacter⟩

end Langlands.Global.RankinSelbergGlobal.ComplexOpenBruhatCoordinates
