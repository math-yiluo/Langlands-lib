import Langlands.Global.RankinSelberg.RealGodementAdditiveJacquet
import Langlands.Representation.Archimedean.RealLeviTorus

/-! # Absolute convergence of the real Jacquet integral in the dominant chamber -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealLeviChartIntegrable

private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ

private abbrev LowerEntryPair (n : ℕ) := CoordC (id : Fin n → Fin n)

private def reverseEntry (n : ℕ) : LowerEntryPair n ≃ UpperEntryPair n where
  toFun q := ⟨(q.val.1.rev, q.val.2.rev), Fin.rev_lt_rev.mpr q.property⟩
  invFun q := ⟨(q.val.1.rev, q.val.2.rev), Fin.rev_lt_rev.mpr q.property⟩
  left_inv _ := Subtype.ext (Prod.ext (Fin.rev_rev _) (Fin.rev_rev _))
  right_inv _ := Subtype.ext (Prod.ext (Fin.rev_rev _) (Fin.rev_rev _))

private def openCellCoordinates (u : N) (q : LowerEntryPair (t + 1)) : ℝ :=
  upperEntryCoordinates (t + 1) u (reverseEntry (t + 1) q)

private theorem measurePreserving_openCellCoordinates (a : ℝˣ) :
    MeasurePreserving (openCellCoordinates (t := t)) (upperStepHaar t a)
      (Measure.pi fun _ : LowerEntryPair (t + 1) => (realSelfDualMeasure a).measure) := by
  let ρ := (realSelfDualMeasure a).measure
  let e := (upperEntryCoordinates (t + 1) (K := ℝ)).toMeasurableEquiv
  let p := MeasurableEquiv.piCongrLeft (fun _ : LowerEntryPair (t + 1) => ℝ)
    (reverseEntry (t + 1)).symm
  have he : MeasurePreserving e.symm (upperEntryProductMeasure (realSelfDualMeasure a) (t + 1))
      (upperStepHaar t a) := ⟨e.symm.measurable, rfl⟩
  have hp := measurePreserving_piCongrLeft (fun _ : LowerEntryPair (t + 1) => ρ)
    (reverseEntry (t + 1)).symm
  have hpoint : p ∘ e = openCellCoordinates (t := t) := by
    funext u q
    change p (e u) q = e u (reverseEntry (t + 1) q)
    simpa only [p, Equiv.symm_apply_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : LowerEntryPair (t + 1) => ℝ)
        (reverseEntry (t + 1)).symm (e u) (reverseEntry (t + 1) q)
  rw [← hpoint]
  exact hp.comp (he.symm e.symm)

private theorem lowerC_openCellCoordinates (u : N) :
    lowerC id (openCellCoordinates u) = (weylLong (t + 1) ℝ * u.val * weylLong (t + 1) ℝ).val := by
  ext i j
  rw [weylLong_conjugate_entry]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [lowerC, Matrix.of_apply, dite_eq_right (show ¬ id j < id i from not_lt.mpr h.le),
      ite_eq_right h.ne,
      UpperUnipotent.entry_eq_zero u (Fin.rev_lt_rev.mpr h)]
  · simp only [lowerC, Matrix.of_apply, id_eq, lt_irrefl, dite_false, ite_true,
      UpperUnipotent.entry_diag]
  · rw [lowerC, Matrix.of_apply, dite_eq_left (show id j < id i from h)]
    exact upperEntryCoordinates_apply u (reverseEntry (t + 1) ⟨(i, j), h⟩)

private def gramExponent (σ : ℕ → ℝ) (j : ℕ) : ℝ := (σ j - σ (j - 1)) / 2

private theorem integrable_openCellGram (a : ℝˣ) (σ : ℕ → ℝ)
    (hσ : ∀ j < t, σ (j + 1) - σ j < -1) :
    Integrable (fun u : N => ∏ l : Fin (t + 1),
      gram l (lowerC id (openCellCoordinates u)) ^ gramExponent σ l) (upperStepHaar t a) := by
  let cl : Fin (t + 1) → Fin (t + 1) := id
  let B := fun x : LowerEntryPair (t + 1) → ℝ =>
    ∏ l : Fin (t + 1), gram l (lowerC cl x) ^ gramExponent σ l
  have hγ (l : Fin (t + 1)) (hl : 0 < l.val) : gramExponent σ l < -(1 / 2) := by
    have hj := hσ (l.val - 1) (by have := l.isLt; omega)
    rw [show l.val - 1 + 1 = l.val by omega] at hj
    unfold gramExponent
    linarith
  have hB : ∀ x, 0 ≤ B x := fun x => Finset.prod_nonneg fun l _ =>
    Real.rpow_nonneg (gram_lowerC_pos (cl := cl) monotone_id x l).le _
  have hVolume : Integrable B := by
    refine ⟨(continuous_prod_gram (cl := cl) monotone_id _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hB)]
    exact gen _ cl monotone_id (gramExponent σ) (fun l hl => (hγ l hl).le)
      (fun k l hkl _ => hγ l (by omega))
  have hHaar : Integrable B (Measure.pi fun _ : LowerEntryPair (t + 1) =>
      (realSelfDualMeasure a).measure) := by
    let r : ℝ≥0 := NNReal.sqrt ‖(a : ℝ)‖₊
    change Integrable B (Measure.pi fun _ : LowerEntryPair (t + 1) => r • (volume : Measure ℝ))
    rw [RectangleTate.pi_smul_eq]
    exact hVolume.smul_measure (by simp)
  exact (measurePreserving_openCellCoordinates a).integrable_comp_of_integrable hHaar

/-- The full open-cell Jacquet integrand is integrable for a continuous function with
upper Borel covariance and strictly dominant shifted diagonal norm exponents. -/
def RealGodementOpenCellConvergenceStatement : Prop :=
  ∀ (t : ℕ) (a : ℝˣ) (f : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (c : (Fin (t + 1) → ℝˣ) → ℂ) (σ : ℕ → ℝ),
    Continuous f →
    (∀ d (u : GeneralLinear.upperUnipotent (t + 1) ℝ) k,
      f (Iwasawa.diagonalUnits d * u.val * k) = c d * f k) →
    (∀ d, ‖c d‖ = ∏ l : Fin (t + 1), |(d l : ℝ)| ^ σ l) →
    (∀ j < t, σ (j + 1) - σ j < -1) →
    ∀ g, Integrable (additiveJacquetKernel a f g) (upperStepHaar t a)

theorem realGodementOpenCellConvergence : RealGodementOpenCellConvergenceStatement := by
  intro t a f c σ hf hCov hNorm hσ g
  let w := weylLong (t + 1) ℝ
  let F := fun k : Langlands.GeneralLinear (t + 1) ℝ => f (k * (w * g))
  have hF : Continuous F := hf.comp (continuous_id.mul continuous_const)
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hF
  have hFCov (d : Fin (t + 1) → ℝˣ) (v : GeneralLinear.upperUnipotent (t + 1) ℝ)
      (k : Langlands.GeneralLinear (t + 1) ℝ) :
      F (Iwasawa.diagonalUnits d * v.val * k) = c d * F k := by
    change f (Iwasawa.diagonalUnits d * v.val * k * (w * g)) = c d * f (k * (w * g))
    rw [mul_assoc (Iwasawa.diagonalUnits d * v.val), hCov]
  have hPhase : Continuous (fun u : GeneralLinear.upperUnipotent (t + 1) ℝ =>
      (standardCharacter (realScaledCharacter a) t u : ℂ)) :=
    Units.continuous_val.comp (standardCharacterContinuous (realScaledCharacter a) t).continuous
  have hKernel : Continuous (additiveJacquetKernel a f g) :=
    (hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)).mul hPhase
  refine Integrable.mono' ((integrable_openCellGram a σ hσ).const_mul C)
    hKernel.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  let y := w * u.val * w
  have hy : gram 0 y.val = 1 := by
    rw [show y.val = _ from (lowerC_openCellCoordinates u).symm,
      RealLeviTorus.gram_zero_eq, det_lowerC monotone_id, one_pow]
  have h := RealLeviTorus.norm_le_gram_fin hFCov hNorm hC y hy
    ((unitaryCompact ℝ (t + 1)).one_mem) (fun l => gramExponent σ l) (fun _ _ => rfl)
  have hFy : F (y * 1) = f (w * u.val * g) := by
    change f ((w * u.val * w) * 1 * (w * g)) = f (w * u.val * g)
    rw [mul_one, mul_assoc (w * u.val), ← mul_assoc w w g,
      show w * w = 1 from weylLong_mul_self (t + 1) ℝ, one_mul]
  rw [hFy, ← lowerC_openCellCoordinates u] at h
  simpa only [additiveJacquetKernel, norm_mul, norm_standardCharacter, mul_one] using h

/-- The full Jacquet integral of a signed-power principal-series vector converges on the
strictly dominant chamber, with the specified real self-dual entry measure. -/
theorem integrable_additiveJacquetKernel_of_mem_principalSeries (a : ℝˣ)
    {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e t)
    {f : G → ℂ} (hf : f ∈ principalSeries ℝ (t + 1) χ) (g : G) :
    Integrable (additiveJacquetKernel a f g) (upperStepHaar t a) := by
  refine realGodementOpenCellConvergence t a f _ (normExponent e (t + 1)) hf.1.continuous
    hf.2 (norm_principalSeriesCharacter hχ _) (fun j hj => ?_) g
  have h := he j hj
  unfold normExponent
  push_cast
  linarith

end Langlands.Global.RankinSelbergGlobal.RealGodement
