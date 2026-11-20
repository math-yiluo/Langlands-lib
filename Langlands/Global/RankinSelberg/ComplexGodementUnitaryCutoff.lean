import Langlands.Global.RankinSelberg.ComplexGodementSection
import Langlands.Analysis.SchwartzCompactAverage
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Smooth invariant cutoffs around the unitary trailing rows -/

noncomputable section

open MeasureTheory Matrix Set
open scoped ContDiff SchwartzMap Matrix.Norms.Operator Langlands.Archimedean.ComplexDuality

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Archimedean.ComplexDuality (unitaryHaar integrable_unitaryHaar)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "K" => unitaryCompact ℂ (n + 1)
local notation "Rect" => Matrix (Fin n) (Fin (n + 1)) ℂ
local notation "Square" => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ

/-- The compact subset of trailing rows of unitary matrices. -/
def unitaryTrailingRows (n : ℕ) : Set (Matrix (Fin n) (Fin (n + 1)) ℂ) :=
  Set.range fun k : unitaryCompact ℂ (n + 1) => trailingRows k.val.val

private theorem continuous_trailingRows : Continuous (trailingRows (m := n)) :=
  continuous_id.matrix_submatrix Fin.succ id

theorem isCompact_unitaryTrailingRows (n : ℕ) : IsCompact (unitaryTrailingRows n) :=
  isCompact_range (continuous_trailingRows.comp (Units.continuous_val.comp continuous_subtype_val))

private theorem trailingRows_mul (A B : Square) : trailingRows (A * B) = trailingRows A * B :=
  (Matrix.submatrix_mul A B Fin.succ id id Function.bijective_id).symm

private def rightAction : Square →ₗ[ℝ] (Rect →L[ℝ] Rect) where
  toFun A := (mulRightLinearMap (Fin n) ℝ A).toContinuousLinearMap
  map_add' A B := by ext X i j; exact congrArg (fun M : Rect => M i j) (Matrix.mul_add X A B)
  map_smul' c A := by ext X i j; exact congrArg (fun M : Rect => M i j) (Matrix.mul_smul X c A)

private def rightPullback (k : K) : Rect →L[ℝ] Rect := rightAction k.val.val

private theorem continuous_rightPullback : Continuous (rightPullback (n := n)) :=
  rightAction.toContinuousLinearMap.continuous.comp (Units.continuous_val.comp continuous_subtype_val)

private theorem rightPullback_inverse (k : K) (X : Rect) :
    rightPullback k⁻¹ (rightPullback k X) = X := by
  change (X * k.val.val) * k.val⁻¹.val = X
  rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

private theorem exists_inverseBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Rect, ∀ k : K, ‖X‖ ≤ C * ‖rightPullback k X‖ := by
  have hc := (continuous_rightPullback (n := n)).comp (continuous_inv (G := K))
  obtain ⟨B, hB⟩ := (isCompact_univ.image hc.norm).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun X k => ?_⟩
  have hb : ‖rightPullback k⁻¹‖ ≤ max B 0 :=
    (hB ⟨k, mem_univ _, rfl⟩).trans (le_max_left _ _)
  conv_lhs => rw [← rightPullback_inverse k X]
  exact ((rightPullback k⁻¹).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- Every invariant open neighborhood of the unitary trailing rows admits a smooth,
right unitary invariant cutoff with compact support in that neighborhood. -/
def ComplexGodementUnitaryCutoffStatement : Prop :=
  ∀ U : Set Rect, IsOpen U → unitaryTrailingRows n ⊆ U →
    (∀ X ∈ U, ∀ k : K, X * k.val.val ∈ U) →
    ∃ χ : 𝓢(Rect, ℂ), HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ X ∈ unitaryTrailingRows n, χ X = 1) ∧
      (∀ (X : Rect) (k : K), χ (X * k.val.val) = χ X) ∧
      ∀ X, ∃ r ∈ Icc (0 : ℝ) 1, χ X = (r : ℂ)

theorem complexGodementUnitaryCutoff : ComplexGodementUnitaryCutoffStatement (n := n) := by
  intro U hU hsub hInv
  let S := unitaryTrailingRows n
  have hS : IsCompact S := isCompact_unitaryTrailingRows n
  obtain ⟨L, hL, hSL, hLU⟩ := exists_compact_between hS hU hsub
  obtain ⟨b, hbD, hbRange, hbSupp, hbOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) isOpen_interior hS.isClosed hSL
  let bC : Rect → ℂ := fun X => (b X : ℂ)
  have hbCsub : tsupport bC ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro X hX
    have hbX : X ∈ Function.support b := fun h => hX (by simp [bC, h])
    rw [hbSupp] at hbX
    exact interior_subset hbX
  have hbC : HasCompactSupport bC := hL.of_isClosed_subset (isClosed_tsupport _) hbCsub
  let Φ : 𝓢(Rect, ℂ) := hbC.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hbD)
  obtain ⟨C, hC, hLower⟩ := exists_inverseBound (n := n)
  let Χ := Langlands.Analysis.SchwartzCompactAverage.average (fun _ : K => (1 : ℂ))
    rightPullback Φ (unitaryHaar (n + 1)) continuous_const continuous_rightPullback hC hLower
  have hΧ (X : Rect) : Χ X = ∫ k : K, bC (X * k.val.val) ∂unitaryHaar (n + 1) := by
    simp only [Χ, Langlands.Analysis.SchwartzCompactAverage.average_apply, one_mul]
    rfl
  let A (p : Rect × K) := p.1 * p.2.val⁻¹.val
  have hA : Continuous A := continuous_fst.matrix_mul
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd).inv)
  let M := A '' (L ×ˢ (Set.univ : Set K))
  have hM : IsCompact M := (hL.prod isCompact_univ).image hA
  have hMsub : M ⊆ U := by
    rintro _ ⟨⟨X, k⟩, ⟨hX, _⟩, rfl⟩
    exact hInv X (hLU hX) k⁻¹
  have hΧsub : tsupport Χ ⊆ M := by
    apply closure_minimal ?_ hM.isClosed
    intro X hX
    by_contra hn
    apply hX
    rw [hΧ]
    apply integral_eq_zero_of_ae
    filter_upwards with k
    by_contra hk
    have hh : X * k.val.val ∈ L := hbCsub (subset_tsupport _ hk)
    apply hn
    refine ⟨(X * k.val.val, k), ⟨hh, mem_univ _⟩, ?_⟩
    exact rightPullback_inverse k X
  refine ⟨Χ, hM.of_isClosed_subset (isClosed_tsupport _) hΧsub, hΧsub.trans hMsub, ?_, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    rw [hΧ]
    have hOne (v : K) : bC (trailingRows k.val.val * v.val.val) = 1 := by
      have hv : trailingRows ((k * v).val.val) ∈ S := ⟨k * v, rfl⟩
      have he : trailingRows k.val.val * v.val.val = trailingRows ((k * v).val.val) :=
        (trailingRows_mul k.val.val v.val.val).symm
      rw [he]
      change (b _ : ℂ) = 1
      rw [(hbOne _).mp hv, Complex.ofReal_one]
    simp_rw [hOne]
    simp
  · intro X k
    rw [hΧ, hΧ, ← integral_mul_left_eq_self (fun v : K => bC (X * v.val.val)) k]
    apply integral_congr_ae
    filter_upwards with v
    change bC ((X * k.val.val) * v.val.val) = bC (X * (k.val.val * v.val.val))
    rw [Matrix.mul_assoc]
  · intro X
    let F : K → ℝ := fun k => b (X * k.val.val)
    have hcont : Continuous F := hbD.continuous.comp
      (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val))
    have hF : Integrable F (unitaryHaar (n + 1)) := integrable_unitaryHaar hcont
    refine ⟨∫ k, F k ∂unitaryHaar (n + 1), ⟨?_, ?_⟩, ?_⟩
    · exact integral_nonneg fun k => (hbRange ⟨_, rfl⟩).1
    · simpa using integral_mono hF (integrable_const (1 : ℝ)) (fun k => (hbRange ⟨_, rfl⟩).2)
    · rw [hΧ]
      exact Complex.ofRealCLM.integral_comp_comm hF

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
