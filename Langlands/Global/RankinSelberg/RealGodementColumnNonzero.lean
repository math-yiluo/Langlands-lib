import Langlands.Analysis.SchwartzCompactFamilies
import Langlands.Global.RankinSelberg.RealGodementCompactSupport
import Langlands.Global.RankinSelberg.RealGodementLeadingFamily
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Compact tests detect nonzero real lower coefficients -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean Langlands.Analysis.SchwartzCompactFamilies
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Metric Set Topology
open scoped ContDiff Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}
local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "V" => (Fin (t + 1) → ℝ)
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

private def columnJoin : (M × V) ≃L[ℝ] X :=
  ({ toFun := fun q => joinFirstColumn q.2 q.1
     invFun := fun A => (A.submatrix id Fin.succ, fun i => A i 0)
     left_inv := fun _ => rfl
     right_inv := fun A => by
       ext i j
       exact Fin.cases rfl (fun _ => rfl) j
     map_add' := fun u v => by
       ext i j
       exact Fin.cases rfl (fun _ => rfl) j
     map_smul' := fun c q => by
       ext i j
       exact Fin.cases rfl (fun _ => rfl) j } : (M × V) ≃ₗ[ℝ] X).toContinuousLinearEquiv

private def columnChart (x : G × V) : X := joinFirstColumn x.2 x.1.val

private theorem isOpenEmbedding_columnChart : IsOpenEmbedding (columnChart (t := t)) :=
  (columnJoin (t := t)).toHomeomorph.isOpenEmbedding.comp
    (Units.isOpenEmbedding_val.prodMap Topology.IsOpenEmbedding.id)

private theorem hasFullRowRank_columnChart (x : G × V) : HasFullRowRank (columnChart x) := by
  let R : Matrix (Fin (t + 2)) (Fin (t + 1)) ℝ := fun i j => Fin.cases 0 (fun k => (x.1⁻¹).val k j) i
  refine ⟨R, ?_⟩
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [columnChart, R, joinFirstColumn_succ, Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add]
  change (x.1.val * (x.1⁻¹).val) i j = _
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

private def columnAmplitude (a : ℝˣ) (W : G → ℂ) (p : ℕ) (s : ℂ) (x : G × V) : ℂ :=
  (realScaledCharacter a).complex (x.2 ⬝ᵥ columnFrequency x.1) *
    (W (columnRepresentative x.1) * (((x.1.val.det / |x.1.val.det| : ℝ) : ℂ) ^ p) *
      Complex.exp (s * (Real.log |x.1.val.det| : ℂ)))

private theorem continuous_columnAmplitude (a : ℝˣ) {W : G → ℂ}
    (hW : Continuous W) (p : ℕ) (s : ℂ) : Continuous (columnAmplitude a W p s) := by
  have hFreq : Continuous (columnFrequency (t := t)) := by
    unfold columnFrequency
    exact (Units.continuous_val.comp (continuous_inverseTranspose (t + 1) ℝ)).matrix_mulVec continuous_const
  have hPair : Continuous (fun q : G × V => q.2 ⬝ᵥ columnFrequency q.1) := by
    unfold dotProduct
    exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_snd).mul
      ((continuous_apply i).comp (hFreq.comp continuous_fst))
  have hRep : Continuous (columnRepresentative (t := t)) := continuous_const.mul continuous_inv
  have hDet : Continuous (fun h : G => h.val.det) := Units.continuous_val.matrix_det
  have hz (h : G) : |h.val.det| ≠ 0 := abs_ne_zero.mpr (determinant h).ne_zero
  have hSign := (Complex.continuous_ofReal.comp (hDet.div hDet.abs hz)).pow p
  have hExp := ((Complex.continuous_ofReal.comp (hDet.abs.log hz)).const_mul s).cexp
  exact ((realScaledCharacter a).continuous_complex.comp hPair).mul
    (((hW.comp hRep).mul hSign |>.mul hExp).comp continuous_fst)

/-- A nonzero continuous lower coefficient gives a nonzero first-column Mellin
value for some Schwartz test of compact full-row-rank support. -/
def RealGodementColumnNonzeroStatement (t : ℕ) : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ)
    (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ), Continuous W → W ≠ 0 →
    ∀ (p : Fin 2) (z : ℂ),
    ∃ (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S ∧
      (∀ x ∈ S, HasFullRowRank x) ∧
      ∃ Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ), (∀ x ∉ S, Φ x = 0) ∧
        godementLeadingFamily D a Φ W p (weylLong (t + 2) ℝ) z ≠ 0

theorem realGodementColumnNonzero : RealGodementColumnNonzeroStatement t := by
  intro D a W hW hWne p z
  have hSome : ∃ g : G, W g ≠ 0 := by
    by_contra! h
    exact hWne (funext h)
  obtain ⟨g, hg⟩ := hSome
  let h := ((weylLong m ℝ)⁻¹ * g)⁻¹
  have hh : columnRepresentative h = g := by
    simp only [columnRepresentative, h, inv_inv, mul_inv_cancel_left]
  let x₀ : G × V := (h, 0)
  let s := z + (t : ℂ) / 2
  let B := columnAmplitude a W p.val s
  have hB : Continuous B := continuous_columnAmplitude a hW p.val s
  have hB0 : B x₀ ≠ 0 := by
    have hSign : ((h.val.det / |h.val.det| : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (div_ne_zero (determinant h).ne_zero (abs_ne_zero.mpr (determinant h).ne_zero))
    have hPhase : (realScaledCharacter a).complex ((0 : V) ⬝ᵥ columnFrequency h) ≠ 0 := by
      rw [← norm_ne_zero_iff, (realScaledCharacter a).norm_complex]
      exact one_ne_zero
    change _ * (W (columnRepresentative h) * _ * _) ≠ 0
    rw [hh]
    exact mul_ne_zero hPhase (mul_ne_zero (mul_ne_zero hg (pow_ne_zero _ hSign)) (Complex.exp_ne_zero _))
  let rot := (B x₀)⁻¹
  have hrot : rot * B x₀ = 1 := inv_mul_cancel₀ hB0
  let O : Set (G × V) := {x | 0 < (rot * B x).re}
  have hO : IsOpen O := isOpen_lt continuous_const (Complex.continuous_re.comp (hB.const_mul rot))
  have hx₀ : x₀ ∈ O := by change 0 < (rot * B x₀).re; rw [hrot]; norm_num
  let j : G × V → X := columnChart
  have hj : IsOpenEmbedding j := isOpenEmbedding_columnChart
  let y₀ := j x₀
  have hy₀ : y₀ ∈ j '' O := mem_image_of_mem _ hx₀
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp (hj.isOpenMap O hO) y₀ hy₀
  let β : ContDiffBump y₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let S := closedBall y₀ β.rOut
  have hS : IsCompact S := isCompact_closedBall _ _
  have hSO : S ⊆ j '' O :=
    (closedBall_subset_ball (show β.rOut < ε by dsimp [β]; linarith)).trans hεO
  have hRank (x : X) (hx : x ∈ S) : HasFullRowRank x := by
    obtain ⟨q, _, rfl⟩ := hSO hx
    exact hasFullRowRank_columnChart q
  have hZero (x : X) (hx : x ∉ S) : (β x : ℂ) = 0 := by
    have hd : β.rOut ≤ dist x y₀ := le_of_lt (not_le.mp hx)
    rw [β.zero_of_le_dist hd, Complex.ofReal_zero]
  let Φ := ofCompactSupport (fun x => (β x : ℂ)) (Complex.ofRealCLM.contDiff.comp β.contDiff) S hS hZero
  refine ⟨S, hS, hRank, Φ, hZero, ?_⟩
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → ℝ))
  let : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
  let μ := D.groupHaar
  let ν := rowMeasure (realSelfDualMeasure a) m
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite D.groupHaar := inferInstance
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite μ := ‹SigmaFinite D.groupHaar›
  let : (realSelfDualMeasure a).measure.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  let : ν.IsAddHaarMeasure := rowMeasure_isAddHaar _ _
  let F (q : G × V) := Φ (j q) * (rot * B q)
  have hF : Continuous F := (Φ.continuous.comp hj.continuous).mul (hB.const_mul rot)
  have hFc : HasCompactSupport F := by
    have hRange : S ⊆ range j := hSO.trans (image_subset_range _ _)
    have hP := hj.isInducing.isCompact_preimage' hS hRange
    apply HasCompactSupport.of_support_subset_isCompact hP
    intro q hq
    by_contra hn
    exact hq (by dsimp [F]; rw [show Φ (j q) = 0 from hZero _ hn, zero_mul])
  have hi : Integrable F (μ.prod ν) := hF.integrable_of_hasCompactSupport hFc
  have hF₀ : F x₀ = 1 := by
    change (β y₀ : ℂ) * (rot * B x₀) = 1
    rw [hrot, mul_one, β.one_of_mem_closedBall (mem_closedBall_self β.rIn_pos.le), Complex.ofReal_one]
  have hPos (q : G × V) : 0 ≤ (F q).re := by
    by_cases hq : j q ∈ S
    · obtain ⟨q', hq', hEq⟩ := hSO hq
      have hqO : q ∈ O := hj.injective hEq ▸ hq'
      change 0 ≤ ((β (j q) : ℂ) * (rot * B q)).re
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg β.nonneg (le_of_lt hqO)
    · simp only [F, show Φ (j q) = 0 from hZero _ hq, zero_mul, Complex.zero_re, le_refl]
  have hIreal := integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp hF) (Complex.reCLM.integrable_comp hi) hPos
    (x := x₀) (by
      change (F x₀).re ≠ 0
      rw [hF₀, Complex.one_re]
      exact one_ne_zero)
  change 0 < ∫ q, RCLike.re (F q) ∂μ.prod ν at hIreal
  rw [integral_re hi] at hIreal
  have he : (∫ q, F q ∂μ.prod ν) = rot * ∫ q, columnMellinIntegrand a Φ W p.val s q ∂μ := by
    rw [integral_prod F hi, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    change (∫ x, F (q, x) ∂ν) = rot * columnMellinIntegrand a Φ W p.val s q
    rw [columnMellinIntegrand, columnMellinBase, firstColumnFourier_apply]
    let c := W (columnRepresentative q) * (((q.val.det / |q.val.det| : ℝ) : ℂ) ^ p.val) *
      Complex.exp (s * (Real.log |q.val.det| : ℂ))
    have hFq (x : V) : F (q, x) =
        (Φ (joinFirstColumn x q.val) * (realScaledCharacter a).complex (x ⬝ᵥ columnFrequency q)) * (rot * c) := by
      simp only [F, B, columnAmplitude, j, columnChart, c]
      ring
    simp only [hFq, integral_mul_const, c]
    ring
  have hIne : (∫ q, columnMellinIntegrand a Φ W p.val s q ∂μ) ≠ 0 := by
    intro hzero
    rw [he, hzero, mul_zero, RCLike.zero_re] at hIreal
    exact (lt_irrefl 0 hIreal)
  have hΦ : rectangularTranslate (1 : G) (1 : H) Φ = Φ := by
    ext x
    simp
  unfold godementLeadingFamily godementColumnValue
  rw [weylLong_mul_self, map_one, hΦ, one_mul]
  exact hIne

end Langlands.Global.RankinSelbergGlobal.RealGodement
