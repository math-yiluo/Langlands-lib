import Langlands.Global.RankinSelberg.RealBruhatGeneratorField
import Langlands.HarmonicAnalysis.Distribution.ChartJacobianDensity
import Langlands.HarmonicAnalysis.Distribution.WeightedVectorField

/-! # Infinitesimal covariance excludes support on a lower real Bruhat cell -/

noncomputable section

open Langlands.GeneralLinear Langlands.GeneralLinear.RealBruhatProductChart
open Langlands.HarmonicAnalysis
open Set TopologicalSpace
open scoped ContDiff Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBruhatChartVanishing

open RealBruhatGeneratorField RealBruhatNormalAction RealBruhatRootStabilizer

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "I" => Fin (r + 1) × Fin (r + 1)

/-- The left and right matrix entry directions. -/
abbrev DirectionIndex (r : ℕ) :=
  (Fin (r + 1) × Fin (r + 1)) ⊕ (Fin (r + 1) × Fin (r + 1))

/-- A strict upper matrix unit, with zero direction at other positions. -/
def upperEntryDirection (ij : I) : M :=
  if ij.1 < ij.2 then Matrix.single ij.1 ij.2 1 else 0

/-- Infinitesimal left or right multiplication by an upper entry direction. -/
def ambientField : DirectionIndex r → M →L[ℝ] M :=
  Sum.elim (fun j => (LinearMap.mulLeft ℝ (upperEntryDirection j)).toContinuousLinearMap)
    (fun j => (LinearMap.mulRight ℝ (upperEntryDirection j)).toContinuousLinearMap)

private def adjacentSum : M →ₗ[ℝ] ℝ where
  toFun A := ∑ j : Fin r, A j.castSucc j.succ
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' t A := by
    change (∑ j : Fin r, t * A j.castSucc j.succ) = t * ∑ j : Fin r, A j.castSucc j.succ
    rw [Finset.mul_sum]

/-- The real factor of the infinitesimal Whittaker character of a direction. -/
def characterWeight : DirectionIndex r → ℝ :=
  Sum.elim (fun _ => 0) (fun j => adjacentSum (upperEntryDirection j))

theorem characterWeight_inl (ij : I) : characterWeight (Sum.inl ij) = 0 := rfl

theorem characterWeight_inr (ij : I) :
    characterWeight (Sum.inr ij) = ∑ j : Fin r, upperEntryDirection ij j.castSucc j.succ := rfl

/-- The open product test domain of a real Bruhat chart. -/
def chartDomain (w : Equiv.Perm (Fin (r + 1))) : Opens (Tangent w × Normal w) :=
  productTestDomain ⟨tangentDomain w, isOpen_tangentDomain w⟩ ⊤

theorem chartDomain_eq_chartSource (w : Equiv.Perm (Fin (r + 1))) :
    chartDomain w = chartSource (productChart w) := rfl

/-- The coordinate vector field for a fixed matrix entry direction. -/
def coordinateField (w : Equiv.Perm (Fin (r + 1))) (j : DirectionIndex r) :
    Tangent w × Normal w → Tangent w × Normal w :=
  chartVectorField (productChart w) (ambientField j)

theorem contDiffOn_coordinateField (w : Equiv.Perm (Fin (r + 1))) (j : DirectionIndex r) :
    ContDiffOn ℝ ∞ (coordinateField w j) (chartDomain w) :=
  contDiffOn_chartVectorField (contDiffOn_productChart w) (contDiffOn_productChart_symm w)
    (ambientField j).contDiff.contDiffOn

private def weight (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (j : DirectionIndex r)
    (z : Tangent w × Normal w) : ℝ :=
  Sum.elim (fun p : I => leftField w i z.1 p.1 p.2)
    (fun p : I => rightField w i z.1 p.1 p.2) j

private theorem contDiffOn_weight (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (j : DirectionIndex r) :
    ContDiffOn ℝ ∞ (weight w i j) (chartDomain w) := by
  have hfst : MapsTo (Prod.fst : Tangent w × Normal w → Tangent w)
      (chartDomain w : Set (Tangent w × Normal w)) (tangentDomain w) := fun _ hz => hz.1
  cases j with
  | inl p =>
    exact (Langlands.Archimedean.PrincipalSeriesExtension.contDiff_entry p.1 p.2).comp_contDiffOn
      ((contDiffOn_leftField w i).comp contDiff_fst.contDiffOn hfst)
  | inr p =>
    exact (Langlands.Archimedean.PrincipalSeriesExtension.contDiff_entry p.1 p.2).comp_contDiffOn
      ((contDiffOn_rightField w i).comp contDiff_fst.contDiffOn hfst)

private theorem sum_weightedEntryDirection (A : M)
    (hA : A.IsUpperTriangular) (hd : ∀ j, A j j = 0) :
    (∑ p : I, A p.1 p.2 • upperEntryDirection p) = A := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single A, ← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro p _
  unfold upperEntryDirection
  split_ifs with hp
  · rw [Matrix.smul_single, smul_eq_mul, mul_one]
  · have hz : A p.1 p.2 = 0 := by
      rcases (le_of_not_gt hp).lt_or_eq with h | h
      · exact hA h
      · rw [h, hd]
    simp only [hz, smul_zero, Matrix.single_zero]

private theorem sum_ambientField (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (hi : w i.castSucc < w i.succ) (z : Tangent w × Normal w)
    (hz : z ∈ chartDomain w) (Y : M) :
    (∑ j : DirectionIndex r, weight w i j z • ambientField j Y) =
      leftField w i z.1 * Y + Y * rightField w i z.1 := by
  obtain ⟨b, v, hb, hv, _⟩ := exists_factors w z.1 hz.1
  have hleft := leftGenerator_strictUpper b w i hi
  have hright := rightGenerator_strictUpper v i
  have hl : (∑ p : I, weight w i (Sum.inl p) z • ambientField (Sum.inl p) Y) =
      (LinearMap.mulRight ℝ Y) (∑ p : I, leftField w i z.1 p.1 p.2 • upperEntryDirection p) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => (map_smul (LinearMap.mulRight ℝ Y) _ _).symm
  have hr : (∑ p : I, weight w i (Sum.inr p) z • ambientField (Sum.inr p) Y) =
      (LinearMap.mulLeft ℝ Y) (∑ p : I, rightField w i z.1 p.1 p.2 • upperEntryDirection p) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => (map_smul (LinearMap.mulLeft ℝ Y) _ _).symm
  rw [Fintype.sum_sum_type, hl, hr, leftField_eq w i z.1 b hb, rightField_eq w i z.1 v hv,
    sum_weightedEntryDirection _ hleft.1 hleft.2, sum_weightedEntryDirection _ hright.1 hright.2]
  rfl

private theorem sum_characterWeight (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (z : Tangent w × Normal w) (hz : z ∈ chartDomain w) :
    (∑ j : DirectionIndex r, characterWeight j * weight w i j z) = 1 := by
  obtain ⟨_, v, _, hv, _⟩ := exists_factors w z.1 hz.1
  have hright := rightGenerator_strictUpper v i
  rw [Fintype.sum_sum_type]
  change (∑ p : I, 0 * leftField w i z.1 p.1 p.2) +
    (∑ p : I, adjacentSum (upperEntryDirection p) * rightField w i z.1 p.1 p.2) = 1
  simp only [zero_mul, Finset.sum_const_zero, zero_add]
  calc
    _ = adjacentSum (∑ p : I, rightField w i z.1 p.1 p.2 • upperEntryDirection p) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [map_smul, smul_eq_mul, mul_comm]
    _ = 1 := by
      rw [rightField_eq w i z.1 v hv, sum_weightedEntryDirection _ hright.1 hright.2]
      exact sum_rightGenerator v i

private theorem sum_coordinateField (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (hi : w i.castSucc < w i.succ) (z : Tangent w × Normal w) (hz : z ∈ chartDomain w)
    (y : Tangent w × Normal w) :
    (∑ j, weight w i j z • coordinateField w j y) =
      fderiv ℝ (productChart w).symm (productChart w y)
        (leftField w i z.1 * productChart w y + productChart w y * rightField w i z.1) := by
  let J := fderiv ℝ (productChart w).symm (productChart w y)
  change (∑ j, weight w i j z • J (ambientField j (productChart w y))) = J _
  simp only [← map_smul J]
  rw [← map_sum, sum_ambientField w i hi z hz]

private theorem trace_frozen_field (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (hi : w i.castSucc < w i.succ) (x : Tangent w) (hx : x ∈ tangentDomain w) :
    LinearMap.trace ℝ (Tangent w × Normal w)
      (fderiv ℝ (fun y => ∑ j, weight w i j (x, 0) • coordinateField w j y) (x, 0)).toLinearMap = 0 := by
  obtain ⟨b, v, hb, hv, _⟩ := exists_factors w x hx
  let e := productChart w
  let z : Tangent w × Normal w := (x, 0)
  have hz : z ∈ e.source := ⟨hx, mem_univ _⟩
  let A := ambientGenerator b v w i
  let Q := chartFDerivEquiv (contDiffOn_productChart w) (contDiffOn_productChart_symm w) hz
  let J' (p : Tangent w × Normal w) := fderiv ℝ e.symm (e p)
  have heq : (fun y => ∑ j, weight w i j z • coordinateField w j y) =
      fun y => J' y (A (e y)) := by
    funext y
    rw [sum_coordinateField w i hi z hz y, leftField_eq w i x b hb, rightField_eq w i x v hv]
    rfl
  have hA : A (productChart w z) = 0 := by
    apply Q.symm.injective
    rw [map_zero]
    change J' z (A (e z)) = 0
    change J' z (leftGenerator b w i * e z + e z * rightGenerator v i) = 0
    rw [← leftField_eq w i x b hb, ← rightField_eq w i x v hv]
    exact pairedField_zero w i x hx
  have hd := ((contDiffOn_productChart w).contDiffAt (e.open_source.mem_nhds hz)).differentiableAt
    (by simp)
  have hJ' : ContDiffOn ℝ ∞ J' e.source :=
    ((contDiffOn_productChart_symm w).fderiv_of_isOpen e.open_target (by simp)).comp
      (contDiffOn_productChart w) (fun _ h => e.map_source h)
  have hD := (((hJ'.contDiffAt (e.open_source.mem_nhds hz)).differentiableAt
    (by simp)).hasFDerivAt.clm_apply (A.hasFDerivAt.comp z hd.hasFDerivAt)).fderiv
  have hequiv : (fderiv ℝ (fun y => J' y (A (e y))) z).toLinearMap =
      Q.symm.toLinearEquiv.conj A.toLinearMap := by
    apply LinearMap.ext
    intro p
    have h := DFunLike.congr_fun hD p
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, hA, map_zero, add_zero] at h
    change (fderiv ℝ (fun y => J' y (A (productChart w y))) z) p =
      J' z (A (fderiv ℝ (productChart w) z p))
    exact h
  rw [heq, hequiv, LinearMap.trace_conj']
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (isNilpotent_pairedGenerator b v w i)).eq_zero

private theorem fieldWeightDerivative_eq_zero (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (hi : w i.castSucc < w i.succ) (x : Tangent w) (hx : x ∈ tangentDomain w) :
    fieldWeightDerivative (coordinateField w) (weight w i) (x, 0) = 0 := by
  have hz : (x, 0) ∈ chartDomain w := ⟨hx, mem_univ _⟩
  have h := trace_fderiv_weightedVectorField (contDiffOn_coordinateField w) (contDiffOn_weight w i)
    (W := pairedField w i) (fun y hy => (sum_coordinateField w i hi y hy y).symm) hz
  rw [trace_fderiv_pairedField_eq_zero w i hi x hx, trace_frozen_field w i hi x hx, zero_add] at h
  exact h.symm

/-- Left invariance and right infinitesimal Whittaker covariance in chart coordinates. -/
def IsChartWhittakerCovariant (w : Equiv.Perm (Fin (r + 1))) (T : 𝓓'(chartDomain w, ℂ))
    (eigen : ℂ) : Prop :=
  ∀ j (f : 𝓓(chartDomain w, ℝ)), T
      (smoothVectorFieldDerivativeTest (contDiffOn_coordinateField w j) f) =
    eigen * (characterWeight j • T f)

/-- A distribution on a lower chart with the given left and right
infinitesimal laws cannot be supported on the cell. -/
theorem chartDistribution_eq_zero_of_covariance (w : Equiv.Perm (Fin (r + 1)))
    (hw : w ≠ Fin.revPerm) (T : 𝓓'(chartDomain w, ℂ))
    (hs : Distribution.IsVanishingOn T {z : Tangent w × Normal w | z.2 ≠ 0})
    (eigen : ℂ) (heigen : eigen ≠ 0) (hT : IsChartWhittakerCovariant w T eigen) : T = 0 := by
  obtain ⟨i, hi⟩ := exists_adjacent_ascent w hw
  have hW := contDiffOn_pairedField w i
  have hβ := contDiffOn_weight w i
  have hV := contDiffOn_coordinateField w
  have hcov := eval_weightedVectorFieldDerivativeTest hV hβ hW
    (fun y hy => (sum_coordinateField w i hi y hy y).symm)
    T eigen characterWeight hT (sum_characterWeight w i)
  exact distribution_eq_zero_of_zeroSection_field hW (contDiffOn_fieldWeightDerivative hV hβ)
    (mem_univ _) (fun x hx => ⟨pairedField_zero w i x hx, fieldWeightDerivative_eq_zero w i hi x hx⟩)
    (fderiv_pairedField_isNilpotent w i hi) T hs eigen heigen hcov

/-- Infinitesimal Whittaker covariance removes the zero section of a lower
real Bruhat chart from the support of a chart distribution. -/
def RealBruhatChartVanishingStatement : Prop :=
  ∀ (r : ℕ) (w : Equiv.Perm (Fin (r + 1))), w ≠ Fin.revPerm →
    ∀ T : 𝓓'(chartDomain w, ℂ), Distribution.IsVanishingOn T {z : Tangent w × Normal w | z.2 ≠ 0} →
      ∀ eigen : ℂ, eigen ≠ 0 → IsChartWhittakerCovariant w T eigen → T = 0

theorem realBruhatChartVanishing : RealBruhatChartVanishingStatement :=
  fun _ w hw => chartDistribution_eq_zero_of_covariance w hw

end Langlands.Global.RankinSelbergGlobal.RealBruhatChartVanishing
