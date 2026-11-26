import Langlands.Global.RankinSelberg.RealModulusOpenCell
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # The real compact picture in opposite-cell coordinates -/

noncomputable section

open Matrix Set Filter
open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealOppositeCompactChart

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.GramFormula (gramExpression complexify)
open Langlands.Archimedean.PrincipalSeriesExtension (extension extension_unitary signedOrthogonalPart
  contDiffOn_gramExpression extension_eq_gramExpression signedOrthogonal signedOrthogonal_mul)
open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_symm_upper)
open RealModulusOpenCell (groupTranspose groupTranspose_val)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "UC" => fun n => Matrix.unitaryGroup (Fin n) ℝ
local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℝ

/-- The vector of all strictly upper entries. -/
abbrev Coordinates (n : ℕ) := UpperEntryPair n → ℝ

variable {n : ℕ}

/-- Transpose the upper-unitriangular matrix with the given entries. -/
def oppositePoint (z : Coordinates n) : G n :=
  groupTranspose ((upperEntryCoordinates (K := ℝ) n).symm z).val

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
  let u := (upperEntryCoordinates (K := ℝ) n).symm z
  ext i j
  change (groupTranspose u.val).val i j = _
  simp only [groupTranspose_val, Matrix.transpose_apply, Matrix.add_apply, lowerLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  rcases lt_trichotomy j i with hji | rfl | hij
  · simp only [dite_eq_left hji, Matrix.one_apply_ne hji.ne', zero_add]
    exact upperEntryCoordinates_symm_upper z hji
  · simp only [Langlands.GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq,
      dite_eq_right (lt_irrefl j), add_zero]
  · simp only [Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero u hij, Matrix.one_apply_ne hij.ne,
      dite_eq_right hij.not_gt, add_zero]

@[simp] theorem oppositePoint_zero (n : ℕ) : oppositePoint (0 : Coordinates n) = 1 := by
  apply Units.ext
  rw [oppositePoint_val, map_zero, add_zero, Units.val_one]

theorem contDiff_oppositePoint_val (n : ℕ) : ContDiff ℝ ∞ (fun z : Coordinates n => (oppositePoint z).val) := by
  simp_rw [oppositePoint_val]
  exact contDiff_const.add (lowerLinear n).toContinuousLinearMap.contDiff

/-- Scalar factor of the upper-Borel extension on the opposite cell. -/
def oppositeScalar (s : Fin n → ℂ) (z : Coordinates n) : ℂ :=
  gramExpression s 1 (complexify (oppositePoint z).val)

/-- Compact factor of the upper-Borel extension on the opposite cell. -/
def oppositeCompact (z : Coordinates n) : UC n := signedOrthogonalPart (oppositePoint z)

theorem extension_oppositePoint (s : Fin n → ℂ) (φ : UC n → ℂ) (z : Coordinates n) :
    extension s φ (oppositePoint z) = oppositeScalar s z * φ (oppositeCompact z) := rfl

private theorem contDiff_gramExpression_opposite (s : Fin n → ℂ)
    (P : MvPolynomial (Fin n × Fin n) ℂ) :
    ContDiff ℝ ∞ (fun z : Coordinates n =>
      gramExpression s P (complexify (oppositePoint z).val)) := by
  apply contDiffOn_univ.mp
  exact (contDiffOn_gramExpression s P).comp (contDiff_oppositePoint_val n).contDiffOn
    (fun z _ => Units.isUnit (oppositePoint z))

theorem contDiff_oppositeScalar (s : Fin n → ℂ) : ContDiff ℝ ∞ (oppositeScalar s) :=
  contDiff_gramExpression_opposite s 1

private def assembleEntries (n : ℕ) : ((Fin n × Fin n) → ℝ) →ₗ[ℝ] Mat n where
  toFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem entry_signedOrthogonalPart (x : G n) (ij : Fin n × Fin n) :
    (((signedOrthogonalPart x : UC n) : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ) =
      gramExpression 0 (MvPolynomial.X ij) (complexify (x : Matrix (Fin n) (Fin n) ℝ)) := by
  have h := extension_eq_gramExpression (n := n) 0
    (φ := fun κ : UC n => ((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ))
    (P := MvPolynomial.X ij) (fun κ => by simp) x
  rw [← h]
  simp [extension, gramExpression]

theorem contDiff_oppositeCompact_val (n : ℕ) :
    ContDiff ℝ ∞ (fun z : Coordinates n => (oppositeCompact z).val) := by
  let H (z : Coordinates n) (ij : Fin n × Fin n) : ℝ :=
    Complex.reCLM (gramExpression 0 (MvPolynomial.X ij) (complexify (oppositePoint z).val))
  have hH : ContDiff ℝ ∞ H := contDiff_pi.mpr fun ij =>
    Complex.reCLM.contDiff.comp (contDiff_gramExpression_opposite 0 (MvPolynomial.X ij))
  have he : (fun z : Coordinates n => (oppositeCompact z).val) =
      fun z => assembleEntries n (H z) := by
    funext z
    ext i j
    change ((signedOrthogonalPart (oppositePoint z) : UC n) : Matrix (Fin n) (Fin n) ℝ) i j =
      Complex.re (gramExpression 0 (MvPolynomial.X (i, j)) (complexify (oppositePoint z).val))
    rw [← entry_signedOrthogonalPart (oppositePoint z) (i, j), Complex.ofReal_re]
  rw [he]
  exact (assembleEntries n).toContinuousLinearMap.contDiff.comp hH

@[simp] theorem oppositeScalar_zero (s : Fin n → ℂ) : oppositeScalar s 0 = 1 := by
  have h := extension_unitary s (fun _ : UC n => (1 : ℂ)) 1
  rw [map_one] at h
  simpa only [oppositeScalar, oppositePoint_zero, extension, mul_one] using h

@[simp] theorem oppositeCompact_zero (n : ℕ) : oppositeCompact (0 : Coordinates n) = 1 := by
  apply Subtype.ext
  change signedOrthogonal ((oppositePoint (0 : Coordinates n)).val) = 1
  rw [oppositePoint_zero, Units.val_one]
  have h := signedOrthogonal_mul (n := n) (b := 1) (κ := 1) Matrix.blockTriangular_one
    (fun l => by simp) (by simp)
  rw [Matrix.one_mul] at h
  rw [h]
  ext i j
  simp [Matrix.one_apply, Langlands.Archimedean.GramFormula.signReal]

/-- Near the opposite-cell origin, the compact Iwasawa factor and scalar factor have
first-order displacement bounds in the exact upper-entry coordinates. -/
def RealOppositeCompactChartStatement : Prop :=
  ∀ (n : ℕ) (s : Fin n → ℂ), ∃ (ρ : ℝ) (C : ℝ), 0 < ρ ∧ 0 ≤ C ∧
    ∀ z : Coordinates n, ‖z‖ < ρ →
      ‖oppositeScalar s z - 1‖ ≤ C * ‖z‖ ∧ ‖(oppositeCompact z).val - 1‖ ≤ C * ‖z‖

theorem realOppositeCompactChart : RealOppositeCompactChartStatement := by
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

end Langlands.Global.RankinSelbergGlobal.RealOppositeCompactChart
