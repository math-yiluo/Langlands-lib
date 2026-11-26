import Langlands.Global.RankinSelberg.RealOppositeMoment
import Langlands.Global.RankinSelberg.RealGodementCompactProfile

/-! # Polynomial growth of the scalar extension factor on the real opposite cell -/

noncomputable section

open scoped Classical Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealOppositeScalarGrowth

open Langlands.Archimedean (principalSeries principalSeriesCharacter realPositionCharacter
  unitaryCompact)
open Langlands.Archimedean.GramFormula (shiftedExponent realPositionExponent signUnit signReal)
open Langlands.Archimedean.RealGramFunction (gramFunction gramFunction_eq_extension HasSignParity
  gramFunction_mem_principalSeries orthogonalEval principalSeriesCharacter_signUnit)
open Langlands.Archimedean.PrincipalSeriesExtension (extension extension_unitary)
open Langlands.GeneralLinear (upperEntryCoordinates)
open RealGodementProfiles (characterList realPositionCharacter_characterList
  realPositionExponent_characterList)
open RealModulusOpenCell (groupTranspose groupTranspose_val)
open RealOppositeCompactChart (Coordinates oppositePoint oppositeScalar extension_oppositePoint
  oppositePoint_upperEntries)
open RealOppositeMoment (norm_upperEntries realMatrixHeight_transpose_le)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "UC" => fun n => Matrix.unitaryGroup (Fin n) ℝ

private def scalarExponent {n : ℕ} (s : Fin n → ℂ) (i : Fin n) : ℂ :=
  s i - (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))

private theorem shiftedExponent_scalar {n : ℕ} (s : Fin n → ℂ) :
    shiftedExponent n (realPositionExponent (characterList 0 (scalarExponent s))) = s := by
  funext i
  simp only [shiftedExponent, realPositionExponent_characterList, scalarExponent]
  ring

private theorem one_parity {n : ℕ} (s : Fin n → ℂ) :
    HasSignParity (realPositionCharacter (characterList 0 (scalarExponent s)))
      (1 : MvPolynomial (Fin n × Fin n) ℂ) := by
  intro a Y
  simp only [map_one, mul_one]
  symm
  refine Finset.prod_eq_one fun l _ => ?_
  rw [realPositionCharacter_characterList]
  unfold signUnit
  split_ifs
  · simp [Langlands.Archimedean.RealJacquetFrobenius.charFun]
  · rw [Units.val_neg, Units.val_one, Langlands.Archimedean.RealJacquetFrobenius.charFun_neg_one]
    simp

private theorem scalar_mem {n : ℕ} (s : Fin n → ℂ) :
    extension s (fun _ : UC n => (1 : ℂ)) ∈
      principalSeries ℝ n (realPositionCharacter (characterList 0 (scalarExponent s))) := by
  have h := gramFunction_mem_principalSeries (n := n)
    (realPositionExponent (characterList 0 (scalarExponent s)))
    (Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.isSignedPower _).eq (one_parity s)
  rw [shiftedExponent_scalar, gramFunction_eq_extension] at h
  convert h using 2
  funext κ
  simp [orthogonalEval]

/-- For each fixed parameter, the opposite-cell scalar factor grows at most polynomially in
the exact upper-entry supremum norm. -/
def RealOppositeScalarGrowthStatement : Prop :=
  ∀ (r : ℕ) (s : Fin (r + 1) → ℂ), ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
    ∀ z : Coordinates (r + 1), ‖oppositeScalar s z‖ ≤ C * (1 + ‖z‖) ^ M

theorem realOppositeScalarGrowth : RealOppositeScalarGrowthStatement := by
  intro r s
  let n := r + 1
  let f : G n → ℂ := extension s (fun _ : UC n => 1)
  obtain ⟨A, N₀, hA, hHeight⟩ := RealPrincipalSeries.realPrincipalSeriesHeight n (Nat.succ_pos r)
    (characterList 0 (scalarExponent s))
  obtain ⟨Ch, hCh, hH⟩ := realMatrixHeight_transpose_le r
  refine ⟨A * 1 * Ch ^ N₀, 2 * (r + 1 + 1) * N₀, by positivity, fun z => ?_⟩
  let e := upperEntryCoordinates (K := ℝ) n
  let u := e.symm z
  have hz : ‖u.val.val - 1‖ = ‖z‖ := by
    rw [← norm_upperEntries u]
    exact congrArg norm (e.apply_symm_apply z)
  have hpt : oppositePoint z = groupTranspose u.val := by
    rw [← oppositePoint_upperEntries u]
    exact congrArg oppositePoint (e.apply_symm_apply z).symm
  have hK : ∀ k ∈ unitaryCompact ℝ n, ‖f k‖ ≤ 1 := by
    intro k hk
    have : k = Unitary.toUnits (⟨k.val, hk⟩ : UC n) := Units.ext rfl
    rw [this]
    change ‖extension s (fun _ : UC n => (1 : ℂ)) (Unitary.toUnits _)‖ ≤ 1
    rw [extension_unitary]
    simp
  have h0 := hHeight f (scalar_mem s) 1 hK (oppositePoint z)
  have hentries : ∀ i j : Fin n, ‖u.val.val j i‖ ≤ 1 + ‖u.val.val - 1‖ := by
    intro i j
    have h := Matrix.norm_entry_le_entrywise_sup_norm (u.val.val - 1) (i := j) (j := i)
    have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℝ) j i‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    calc
      ‖u.val.val j i‖ = ‖(u.val.val - 1) j i + (1 : Matrix (Fin n) (Fin n) ℝ) j i‖ := by
        rw [Matrix.sub_apply, sub_add_cancel]
      _ ≤ ‖(u.val.val - 1) j i‖ + ‖(1 : Matrix (Fin n) (Fin n) ℝ) j i‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hHt := hH u ‖u.val.val - 1‖ hentries (norm_nonneg _)
  have hf : f (oppositePoint z) = oppositeScalar s z := by
    change extension s (fun _ : UC n => 1) (oppositePoint z) = _
    rw [extension_oppositePoint, mul_one]
  rw [← hf]
  have hHnn : 0 ≤ realMatrixHeight (oppositePoint z) :=
    RealPlaceRestriction.realMatrixHeight_nonneg _
  calc
    _ ≤ A * 1 * realMatrixHeight (oppositePoint z) ^ N₀ := h0
    _ ≤ A * 1 * (Ch * (1 + ‖z‖) ^ (2 * (r + 1 + 1))) ^ N₀ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ hHnn
      rw [hpt, ← hz]
      exact hHt
    _ = _ := by rw [mul_pow, ← pow_mul, ← mul_assoc]

end Langlands.Global.RankinSelbergGlobal.RealOppositeScalarGrowth
