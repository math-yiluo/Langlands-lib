import Langlands.Global.RankinSelberg.ComplexModulusOpenCell
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # The complex compact picture in opposite-cell coordinates -/

noncomputable section

open Matrix Set Filter
open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexOppositeCompactChart

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGramFormula (gramExpression hatCoord)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extension extension_unitary phaseOrth phaseOrthPart
  contDiffOn_gramExpression phaseOrthPart_iwasawa phaseMatrix_one)
open GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_symm_upper)
open ComplexModulusOpenCell (groupTranspose groupTranspose_val)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => GeneralLinear.upperUnipotent n ℂ
local notation "UC" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ

/-- The vector of all strictly upper entries. -/
abbrev Coordinates (n : ℕ) := UpperEntryPair n → ℂ

variable {n : ℕ}

/-- Transpose the upper-unitriangular matrix with the given entries. -/
def oppositePoint (z : Coordinates n) : G n :=
  groupTranspose ((upperEntryCoordinates (K := ℂ) n).symm z).val

theorem oppositePoint_upperEntries (u : N n) : oppositePoint (upperEntryCoordinates n u) = groupTranspose u.val := by
  simp [oppositePoint]

private def lowerLinear (n : ℕ) : Coordinates n →ₗ[ℝ] Mat n where
  toFun z := Matrix.of fun i j => if h : j < i then z ⟨(j, i), h⟩ else 0
  map_add' z w := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' a z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private theorem oppositePoint_val (z : Coordinates n) : (oppositePoint z).val = 1 + lowerLinear n z := by
  let u := (upperEntryCoordinates (K := ℂ) n).symm z
  ext i j
  change (groupTranspose u.val).val i j = _
  simp only [groupTranspose_val, Matrix.transpose_apply, Matrix.add_apply, lowerLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  rcases lt_trichotomy j i with hji | rfl | hij
  · simp only [dite_eq_left hji, Matrix.one_apply_ne hji.ne', zero_add]
    exact upperEntryCoordinates_symm_upper z hji
  · simp only [GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq,
      dite_eq_right (lt_irrefl j), add_zero]
  · simp only [GeneralLinear.UpperUnipotent.entry_eq_zero u hij, Matrix.one_apply_ne hij.ne,
      dite_eq_right hij.not_gt, add_zero]

@[simp] theorem oppositePoint_zero (n : ℕ) : oppositePoint (0 : Coordinates n) = 1 := by
  apply Units.ext
  rw [oppositePoint_val, map_zero, add_zero, Units.val_one]

theorem contDiff_oppositePoint_val (n : ℕ) : ContDiff ℝ ∞ (fun z : Coordinates n => (oppositePoint z).val) := by
  simp_rw [oppositePoint_val]
  exact contDiff_const.add (lowerLinear n).toContinuousLinearMap.contDiff

/-- Scalar factor of the upper-Borel extension on the opposite cell. -/
def oppositeScalar (s : Fin n → ℂ) (z : Coordinates n) : ℂ :=
  gramExpression s 1 (oppositePoint z).val ((oppositePoint z).val.map (starRingEnd ℂ))

/-- Compact factor of the upper-Borel extension on the opposite cell. -/
def oppositeCompact (z : Coordinates n) : UC n := phaseOrthPart (oppositePoint z)

theorem extension_oppositePoint (s : Fin n → ℂ) (φ : UC n → ℂ) (z : Coordinates n) :
    extension s φ (oppositePoint z) = oppositeScalar s z * φ (oppositeCompact z) := rfl

private theorem contDiff_gramExpression_opposite (s : Fin n → ℂ)
    (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    ContDiff ℝ ∞ (fun z : Coordinates n =>
      gramExpression s P (oppositePoint z).val ((oppositePoint z).val.map (starRingEnd ℂ))) := by
  apply contDiffOn_univ.mp
  exact (contDiffOn_gramExpression s P).comp (contDiff_oppositePoint_val n).contDiffOn
    (fun z _ => Units.isUnit (oppositePoint z))

theorem contDiff_oppositeScalar (s : Fin n → ℂ) : ContDiff ℝ ∞ (oppositeScalar s) :=
  contDiff_gramExpression_opposite s 1

private def assembleEntries (n : ℕ) : ((Fin n × Fin n) → ℂ) →ₗ[ℝ] Mat n where
  toFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiff_oppositeCompact_val (n : ℕ) : ContDiff ℝ ∞ (fun z : Coordinates n => (oppositeCompact z).val) := by
  let s : Fin n → ℂ := 0
  let H (z : Coordinates n) (ij : Fin n × Fin n) :=
    gramExpression s (MvPolynomial.X (Sum.inl ij)) (oppositePoint z).val
      ((oppositePoint z).val.map (starRingEnd ℂ))
  have hH : ContDiff ℝ ∞ H := contDiff_pi.mpr fun ij =>
    contDiff_gramExpression_opposite s (MvPolynomial.X (Sum.inl ij))
  have he : (fun z : Coordinates n => (oppositeCompact z).val) = fun z => assembleEntries n (H z) := by
    funext z
    ext i j
    change hatCoord i j (oppositePoint z).val ((oppositePoint z).val.map (starRingEnd ℂ)) = H z (i, j)
    simp only [H, gramExpression, s, Pi.zero_apply, neg_zero, Complex.cpow_zero, mul_one,
      Finset.prod_const_one, MvPolynomial.eval_X, Sum.elim_inl, one_mul]
  rw [he]
  exact (assembleEntries n).toContinuousLinearMap.contDiff.comp hH

@[simp] theorem oppositeScalar_zero (s : Fin n → ℂ) : oppositeScalar s 0 = 1 := by
  have h := extension_unitary s (fun _ : UC n => (1 : ℂ)) 1
  simpa only [oppositeScalar, oppositePoint_zero, map_one, extension, mul_one] using h

@[simp] theorem oppositeCompact_zero (n : ℕ) : oppositeCompact (0 : Coordinates n) = 1 := by
  have hD : GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin n => (1 : ℂˣ)) = 1 :=
    map_one _
  have h := phaseOrthPart_iwasawa (fun _ : Fin n => (1 : ℂˣ)) (1 : N n) (unitaryCompact ℂ n).one_mem
  rw [hD, Subgroup.coe_one, mul_one, mul_one, phaseMatrix_one, one_mul] at h
  rw [oppositeCompact, oppositePoint_zero, h]
  rfl

/-- Near the opposite-cell origin, the compact Iwasawa factor and scalar factor have
first-order displacement bounds in the exact upper-entry coordinates. -/
def ComplexOppositeCompactChartStatement : Prop :=
  ∀ (n : ℕ) (s : Fin n → ℂ), ∃ (ρ : ℝ) (C : ℝ), 0 < ρ ∧ 0 ≤ C ∧
    ∀ z : Coordinates n, ‖z‖ < ρ →
      ‖oppositeScalar s z - 1‖ ≤ C * ‖z‖ ∧ ‖(oppositeCompact z).val - 1‖ ≤ C * ‖z‖

theorem complexOppositeCompactChart : ComplexOppositeCompactChartStatement := by
  intro n s
  have hs : ContDiffAt ℝ 1 (oppositeScalar s) (0 : Coordinates n) :=
    (contDiff_oppositeScalar s).contDiffAt.of_le (by simp)
  have hk : ContDiffAt ℝ 1 (fun z : Coordinates n => (oppositeCompact z).val) 0 :=
    (contDiff_oppositeCompact_val n).contDiffAt.of_le (by simp)
  obtain ⟨C₁, A, hA, hLip₁⟩ := hs.exists_lipschitzOnWith
  obtain ⟨C₂, B, hB, hLip₂⟩ := hk.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hA hB)
  refine ⟨ρ, max (C₁ : ℝ) (C₂ : ℝ), hρ, (C₁.coe_nonneg).trans (le_max_left _ _), fun z hz => ?_⟩
  have h₀ := hsub (Metric.mem_ball_self hρ)
  have hz' := hsub (show z ∈ Metric.ball 0 ρ by rwa [Metric.mem_ball, dist_zero_right])
  have h₁ := hLip₁.dist_le_mul z hz'.1 0 h₀.1
  have h₂ := hLip₂.dist_le_mul z hz'.2 0 h₀.2
  have hz₀ : (oppositeCompact (0 : Coordinates n)).val = (1 : Mat n) :=
    congrArg Subtype.val (oppositeCompact_zero n)
  simp only [dist_eq_norm, sub_zero, oppositeScalar_zero, hz₀] at h₁ h₂
  exact ⟨h₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
    h₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩

end Langlands.Global.RankinSelbergGlobal.ComplexOppositeCompactChart
