import Langlands.Global.RankinSelberg.ComplexJacquetChamberNonzero
import Langlands.Global.RankinSelberg.RealOppositeMoment

/-!
# A compact-finite real standard section with nonzero opposite-cell mass

The moment sections take the value one at the identity, and raising the moment exponent
multiplies their opposite-cell restriction by a power of the inverse Gram product, a weight that
peaks uniformly at the identity. A peak argument therefore produces positive opposite-cell mass.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealOppositeNonzero

open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_apply)
open Langlands.LocalFactor.Archimedean (RealCharacterData RealBlock)
open Langlands.Archimedean.GramFormula (gram)
open ComplexJacquetChamberNonzero (exists_pos_integral_pow_of_peak)
open RealJacquetUnipotentMeasure (entryHaar_isHaar)
open RealModulusOpenCell (realEntryLebesgue groupTranspose)
open RealOppositeGramBound (oppositeGramProduct one_le_oppositeGramProduct realOppositeGramBound)
open RealOppositeMoment (momentSection momentSection_mem momentSection_one momentSection_add_opposite
  continuous_momentSection' norm_upperEntries realOppositeMoment)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℝ
local notation "Std" => Automorphic.realStandardKFinite

local instance realOppositeNonzeroMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance realOppositeNonzeroBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
private theorem continuous_oppositeGramProduct : Continuous (oppositeGramProduct (n := n)) := by
  unfold oppositeGramProduct
  refine continuous_finsetProd _ fun k _ => ?_
  have hc : Continuous (fun u : N n => u.val.valᵀ) :=
    ((Units.continuous_val (M := Mat n)).comp continuous_subtype_val).matrix_transpose
  exact (Langlands.Archimedean.PrincipalSeriesExtension.contDiff_gram (n := n) k.val).continuous.comp hc

private theorem gram_one (k : ℕ) : gram k (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h : Langlands.Archimedean.GramFormula.paddedGram k (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext p q
    simp [Langlands.Archimedean.GramFormula.paddedGram]
  rw [gram, h, Matrix.det_one]

private theorem oppositeGramProduct_one (n : ℕ) : oppositeGramProduct (1 : N n) = 1 := by
  unfold oppositeGramProduct
  refine Finset.prod_eq_one fun k _ => ?_
  simp only [Subgroup.coe_one, Units.val_one, Matrix.transpose_one]
  exact gram_one k.val

private def peakWeight (u : N n) : ℝ := (oppositeGramProduct u)⁻¹

private theorem continuous_peakWeight : Continuous (peakWeight (n := n)) :=
  continuous_oppositeGramProduct.inv₀ fun u =>
    (zero_lt_one.trans_le (one_le_oppositeGramProduct u)).ne'

private theorem entries_one (n : ℕ) : upperEntryCoordinates (K := ℝ) n (1 : N n) = 0 := by
  funext ij
  simp only [upperEntryCoordinates_apply, Subgroup.coe_one, Units.val_one, Pi.zero_apply,
    Matrix.one_apply_ne ij.2.ne]

open scoped Matrix.Norms.Elementwise

private theorem peakWeight_uniform {U : Set (N n)} (hU : IsOpen U) (hU₁ : (1 : N n) ∈ U) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ u ∉ U, peakWeight u ≤ c := by
  let e := upperEntryCoordinates (K := ℝ) n
  let V : Set (UpperEntryPair n → ℝ) := e.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage e.symm.continuous
  have hV₀ : (0 : UpperEntryPair n → ℝ) ∈ V := by
    change e.symm 0 ∈ U
    rw [← entries_one n, e.symm_apply_apply]
    exact hU₁
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV _ hV₀
  let c : ℝ := (1 + δ ^ 2)⁻¹
  have hc : 1 < 1 + δ ^ 2 := lt_add_of_pos_right _ (sq_pos_of_ne_zero hδ.ne')
  refine ⟨c, inv_nonneg.mpr (by positivity), inv_lt_one_of_one_lt₀ hc, fun u hu => ?_⟩
  have hδu : δ ≤ ‖u.val.val - 1‖ := le_of_not_gt fun h => by
    have he : e u ∈ Metric.ball 0 δ := by
      rw [Metric.mem_ball, dist_zero_right, show ‖e u‖ = ‖u.val.val - 1‖ from norm_upperEntries u]
      exact h
    apply hu
    have h := hδV he
    change e.symm (e u) ∈ U at h
    rwa [e.symm_apply_apply] at h
  exact inv_anti₀ (zero_lt_one.trans hc)
    ((add_le_add le_rfl (pow_le_pow_left₀ hδ.le hδu 2)).trans (realOppositeGramBound n u))

/-- In any positive rank and for any real character list, a compact-finite section with any
prescribed polynomial moment can be chosen with strictly positive real part of its opposite-cell
mass. -/
def RealOppositeNonzeroStatement : Prop :=
  ∀ (r : ℕ) (cs : List RealCharacterData) (L : ℕ),
    ∃ f : Std (r + 1) (cs.map RealBlock.character),
    Integrable (fun u : N (r + 1) => (1 + ‖u.val.val - 1‖) ^ L • f.val (groupTranspose u.val))
      (realEntryLebesgue (r + 1)) ∧
    0 < (∫ u : N (r + 1), f.val (groupTranspose u.val) ∂realEntryLebesgue (r + 1)).re

theorem realOppositeNonzero : RealOppositeNonzeroStatement := by
  intro r cs L
  let n := r + 1
  let ds := cs.map RealBlock.character
  let ν := realEntryLebesgue n
  let : ν.IsHaarMeasure := entryHaar_isHaar _ _
  let : LocallyCompactSpace (N n) :=
    (upperEntryCoordinates (K := ℝ) n).isClosedEmbedding.locallyCompactSpace
  obtain ⟨m, hMoment⟩ := realOppositeMoment r ds L
  let F : N n → ℂ := fun u => momentSection n ds m (groupTranspose u.val)
  have hT : Continuous (fun u : N n => groupTranspose u.val) :=
    ((Langlands.GeneralLinear.continuous_inverseTranspose n ℝ).comp continuous_inv).comp
      continuous_subtype_val
  have hF : Continuous F := (continuous_momentSection' ds m).comp hT
  have hF₁ : F 1 = 1 := by
    change momentSection n ds m (groupTranspose ((1 : N n) : Langlands.GeneralLinear n ℝ)) = 1
    rw [show groupTranspose ((1 : N n) : Langlands.GeneralLinear n ℝ) = 1 by
      apply Units.ext; simp]
    exact momentSection_one n ds m
  have hInt : Integrable F ν := by
    refine (hMoment m le_rfl).norm.mono' hF.aestronglyMeasurable (ae_of_all _ fun u => ?_)
    change ‖F u‖ ≤ ‖(1 + ‖u.val.val - 1‖) ^ L • F u‖
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact le_mul_of_one_le_left (norm_nonneg _)
      (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))
  obtain ⟨j, hj⟩ := exists_pos_integral_pow_of_peak ν hF hInt hF₁ continuous_peakWeight
    (fun u => inv_nonneg.mpr ((zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_oppositeGramProduct u)))
    (fun u => inv_le_one_of_one_le₀ (one_le_oppositeGramProduct u))
    (by simp [peakWeight, oppositeGramProduct_one]) (fun _ => peakWeight_uniform)
  refine ⟨⟨momentSection n ds (m + j), momentSection_mem cs (m + j)⟩,
    hMoment (m + j) (Nat.le_add_right m j), ?_⟩
  change 0 < (∫ u : N n, momentSection n ds (m + j) (groupTranspose u.val) ∂ν).re
  simp_rw [momentSection_add_opposite]
  exact hj

end Langlands.Global.RankinSelbergGlobal.RealOppositeNonzero
