import Langlands.Global.RankinSelberg.ComplexGapUpperTail
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRegularity
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-! # The triangular exchange inside the split Godement kernel -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapTailExchange

open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (det_upperUnipotent)
open Langlands.GeneralLinear (rankInclusion determinant)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open Langlands.RankinSelberg (lastRow_unipotent_mul rectangularMeasure)
open ComplexGapUpperTail
open ComplexGapColumnFourier (triangularOrdinary triangularFourier complexGapTriangularFourier)
open ComplexGodementFourier (fourier)
open ComplexJacquetUnipotentMeasure (entryHaar)

variable (k q : ℕ)

local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℂ
local notation "H" => Langlands.GeneralLinear k ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ
local notation "Tail" => Matrix (Fin k) (Fin q) ℂ
local notation "Rect" => Matrix (Fin k) J ℂ
local notation "Mat" => Matrix I I ℂ

local instance exchangeTailMeasurable : MeasurableSpace N := borel _

/-- The leading rectangular, first-column, later-column, and final frequency factors
of a split partial Fourier test. -/
structure SplitTailTest where
  leading : Matrix I (Fin k) ℂ → ℂ
  first : (I → ℂ) → ℂ
  later : Fin q → 𝓢(I → ℂ, ℂ)
  lastFrequency : (I → ℂ) → ℂ

private def leadingColumns (B : G) : Matrix I (Fin k) ℂ := fun i j => B.val i (j.castAdd (q + 1))

private def firstTailColumn (B : G) : I → ℂ := fun i => B.val i ((0 : J).natAdd k)

private theorem packedTail_fix_leading (Y : Rect) (Z : N) (j : Fin k) :
    (fun i : I => (packedTail k q Y Z).val.val i (j.castAdd (q + 1))) =
      fun i => (1 : Mat) i (j.castAdd (q + 1)) := by
  funext i
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [packedTail_top_left]
    by_cases h : i₀ = j
    · subst i₀
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h]
      symm
      apply Matrix.one_apply_ne
      intro e
      exact h (Fin.ext (congrArg (fun i : I => i.val) e))
  · rw [packedTail_bottom_left, Matrix.one_apply_ne]
    intro h
    have he := congrArg Fin.val h
    change k + i₁.val = j.val at he
    omega

private theorem packedTail_fix_first (Y : Rect) (Z : N) (hY : ∀ i, Y i 0 = 0) :
    firstTailColumn k q (packedTail k q Y Z).val = fun i => (1 : Mat) i ((0 : J).natAdd k) := by
  funext i
  change (packedTail k q Y Z).val.val i ((0 : J).natAdd k) = _
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [packedTail_top_right, hY, Matrix.one_apply_ne]
    intro h
    have he := congrArg Fin.val h
    change i₀.val = k + 0 at he
    omega
  · rw [packedTail_bottom_right]
    by_cases h : i₁ = 0
    · subst i₁
      rw [Langlands.GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq]
    · have hi : (0 : J) < i₁ := Fin.pos_iff_ne_zero.mpr h
      rw [Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero Z hi, Matrix.one_apply_ne]
      intro hn
      have he := congrArg Fin.val hn
      change k + i₁.val = k + 0 at he
      exact h (Fin.ext (by omega))

private theorem column_mul_of_fixed (B C : G) (j : I)
    (hC : (fun i => C.val i j) = fun i => (1 : Mat) i j) :
    (fun i => (B * C).val i j) = fun i => B.val i j := by
  change B.val.mulVec (fun i => C.val i j) = _
  rw [hC]
  change (fun i => (B.val * (1 : Mat)) i j) = _
  rw [Matrix.mul_one]

private theorem leadingColumns_mul_packed (B : G) (Y : Rect) (Z : N) :
    leadingColumns k q (B * (packedTail k q Y Z).val) = leadingColumns k q B := by
  funext i j
  exact congrFun (column_mul_of_fixed k q B _ _ (packedTail_fix_leading k q Y Z j)) i

private theorem leadingColumns_mul_packed_rankInclusion (B : G) (Y : Rect) (Z : N) (h : H) :
    leadingColumns k q (B * (packedTail k q Y Z).val * rankInclusion (q + 1) h) =
      leadingColumns k q (B * rankInclusion (q + 1) h) := by
  let A := rankInclusion (q + 1) h
  let R := (packedTail k q Y Z).val
  let R' := (packedTail k q (h⁻¹.val * Y) Z).val
  have hconj : A⁻¹ * R * A = R' := by
    simpa only [A, R, R', map_inv, inv_inv] using packedTail_conj k q h⁻¹ Y Z
  have hMove : R * A = A * R' := by rw [← hconj]; group
  change leadingColumns k q (B * R * A) = leadingColumns k q (B * A)
  rw [mul_assoc, hMove, ← mul_assoc]
  exact leadingColumns_mul_packed k q (B * A) _ Z

private theorem packed_inv_character (a : ℂˣ) (Y : Rect) (Z : N) (hY : ∀ i, Y i 0 = 0) :
    complexWhittakerCharacter (-a) (packedTail k q Y Z)⁻¹.val =
      (Whittaker.standardCharacter (complexScaledCharacter a) q Z : ℂ) := by
  simp only [complexWhittakerCharacter, Whittaker.standardCharacter_apply,
    Langlands.GeneralLinear.UpperUnipotent.inv_adjacent_entry, Finset.sum_neg_distrib]
  rw [packedTail_adjacent_sum k q Y Z hY]
  change Langlands.GodementJacquet.traceCharacter (-a) (-_) = Langlands.GodementJacquet.traceCharacter a _
  rw [Langlands.GodementJacquet.traceCharacter_neg_scale, neg_neg]

private theorem whittaker_mul_packed (a : ℂˣ) (ds : List ComplexCharacterData)
    (W : complexWhittakerModel (k + q) ds (-a)) (g : H) (B : G)
    (Y : Rect) (Z : N) (hY : ∀ i, Y i 0 = 0) :
    W.val (rankInclusion (q + 1) g * (B * (packedTail k q Y Z).val)⁻¹) =
      (Whittaker.standardCharacter (complexScaledCharacter a) q Z : ℂ) *
        W.val (rankInclusion (q + 1) g * B⁻¹) := by
  let A := rankInclusion (q + 1) g
  let R := packedTail k q Y Z
  let R' := packedTail k q (g.val * Y) Z
  have hconj : A * R.val * A⁻¹ = R'.val := packedTail_conj k q g Y Z
  have hFactor : A * (B * R.val)⁻¹ = R'⁻¹.val * (A * B⁻¹) := by
    change A * (B * R.val)⁻¹ = R'.val⁻¹ * (A * B⁻¹)
    rw [← hconj]
    group
  rw [hFactor, complexWhittakerModel_left_equivariant W.2 _ R'⁻¹.2]
  apply congrArg (· * W.val (A * B⁻¹))
  apply packed_inv_character k q a _ Z
  intro i
  simp only [Matrix.mul_apply, hY, mul_zero, Finset.sum_const_zero]

/-- The factor keeping its leading block, first column and last frequency outside
of the triangular column Fourier calculation. -/
def fixedTailFactor (T : SplitTailTest k q) (W : G → ℂ) (χ : ℂˣ →* ℂ) (g h : H) (B : G) : ℂ :=
  T.leading (leadingColumns k q (B * rankInclusion (q + 1) h)) * T.first (firstTailColumn k q B) *
    T.lastFrequency (Langlands.RankinSelberg.lastRow B⁻¹) * W (rankInclusion (q + 1) (g * h⁻¹) * B⁻¹) *
    χ (determinant h) * χ (determinant B)

private theorem fixedTailFactor_mul (T : SplitTailTest k q) (a : ℂˣ) (ds : List ComplexCharacterData)
    (W : complexWhittakerModel (k + q) ds (-a)) (χ : ℂˣ →* ℂ) (g h : H) (B : G)
    (Y : Rect) (Z : N) (hY : ∀ i, Y i 0 = 0) :
    fixedTailFactor k q T W.val χ g h (B * (packedTail k q Y Z).val) =
      fixedTailFactor k q T W.val χ g h B * (Whittaker.standardCharacter (complexScaledCharacter a) q Z : ℂ) := by
  let R := packedTail k q Y Z
  have hFirst : firstTailColumn k q (B * R.val) = firstTailColumn k q B :=
    column_mul_of_fixed k q B R.val _ (packedTail_fix_first k q Y Z hY)
  have hLast : Langlands.RankinSelberg.lastRow (B * R.val)⁻¹ = Langlands.RankinSelberg.lastRow B⁻¹ := by
    rw [mul_inv_rev]
    exact lastRow_unipotent_mul R⁻¹ B⁻¹
  have hdet : determinant (B * R.val) = determinant B := by
    have hR : determinant R.val = 1 := Units.ext (det_upperUnipotent R)
    rw [map_mul, hR, mul_one]
  unfold fixedTailFactor
  rw [leadingColumns_mul_packed_rankInclusion, hFirst, hLast, hdet,
    whittaker_mul_packed k q a ds W _ B Y Z hY]
  ring

/-- An upper rectangle supported in the later columns leaves all retained factors fixed. -/
theorem fixedTailFactor_mul_laterRectangle (T : SplitTailTest k q) (a : ℂˣ)
    (ds : List ComplexCharacterData) (W : complexWhittakerModel (k + q) ds (-a))
    (χ : ℂˣ →* ℂ) (g h : H) (B : G) (Y : Rect) (hY : ∀ i, Y i 0 = 0) :
    fixedTailFactor k q T W.val χ g h (B * (packedTail k q Y 1).val) =
      fixedTailFactor k q T W.val χ g h B := by
  rw [fixedTailFactor_mul k q T a ds W χ g h B Y 1 hY, map_one, Units.val_one, mul_one]

/-- The ordinary block kernel after the first rectangular column has been separated. -/
def ordinaryBlockTailKernel (T : SplitTailTest k q) (W : G → ℂ) (χ : ℂˣ →* ℂ)
    (g h : H) (B : G) (p : Tail × N) : ℂ :=
  let C := B * (packedTail k q (laterRectangle k q p.1) p.2).val
  fixedTailFactor k q T W χ g h C *
    ∏ j : Fin q, T.later j (fun i => C.val i (j.succ.natAdd k))

/-- The alternate block kernel uses the earlier tail positions at the inverse-transpose matrix. -/
def alternateBlockTailKernel (a : ℂˣ) (T : SplitTailTest k q) (W : G → ℂ) (χ : ℂˣ →* ℂ)
    (g h : H) (B : G) (Z : N) : ℂ :=
  let C := B * (packedTail k q 0 Z).val
  fixedTailFactor k q T W χ g h C *
    ∏ j : Fin q, fourier a (T.later j) (fun i => C⁻¹.val.transpose i (j.castSucc.natAdd k))

private theorem inverse_packed_zero (Z : N) : (packedTail k q 0 Z).val⁻¹ = (packedTail k q 0 Z⁻¹).val := by
  rw [← inv_inj, inv_inv]
  apply Units.ext
  change Matrix.reindex (finSumFinEquiv : Fin k ⊕ J ≃ I) finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 Z.val.val) =
    Matrix.reindex (finSumFinEquiv : Fin k ⊕ J ≃ I) finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ)
        (-(0 * Z⁻¹⁻¹.val.val)) 0 Z⁻¹⁻¹.val.val)
  rw [inv_inv, Matrix.zero_mul, neg_zero]

private theorem ordinaryKernel_eq (a : ℂˣ) (T : SplitTailTest k q) (ds : List ComplexCharacterData)
    (W : complexWhittakerModel (k + q) ds (-a)) (χ : ℂˣ →* ℂ) (g h : H) (B : G) (p : Tail × N) :
    ordinaryBlockTailKernel k q T W.val χ g h B p =
      fixedTailFactor k q T W.val χ g h B * triangularOrdinary k q a B T.later p := by
  unfold ordinaryBlockTailKernel triangularOrdinary
  dsimp only
  rw [fixedTailFactor_mul k q T a ds W χ g h B _ p.2 (fun i => by rfl)]
  have hCol (j : Fin q) : (fun i => (B * (packedTail k q (laterRectangle k q p.1) p.2).val).val i
      (j.succ.natAdd k)) = B.val.mulVec (ComplexGapColumnFourier.directColumn k q p.1 p.2 j) := by
    rw [← packedTail_laterColumn]
    rfl
  simp only [hCol]
  ring

/-- The complete alternate kernel factors through the triangular Fourier kernel. -/
theorem alternateKernel_eq (a : ℂˣ) (T : SplitTailTest k q) (ds : List ComplexCharacterData)
    (W : complexWhittakerModel (k + q) ds (-a)) (χ : ℂˣ →* ℂ) (g h : H) (B : G) (Z : N) :
    alternateBlockTailKernel k q a T W.val χ g h B Z =
      fixedTailFactor k q T W.val χ g h B * triangularFourier k q a B T.later Z := by
  unfold alternateBlockTailKernel triangularFourier
  dsimp only
  rw [fixedTailFactor_mul k q T a ds W χ g h B 0 Z (fun i => by rfl)]
  have hCol (j : Fin q) : (fun i => (B * (packedTail k q 0 Z).val)⁻¹.val.transpose i
      (j.castSucc.natAdd k)) = B⁻¹.val.transpose.mulVec (ComplexGapColumnFourier.transposeColumn k q Z⁻¹ j) := by
    rw [mul_inv_rev, inverse_packed_zero, Units.val_mul, Matrix.transpose_mul, ← packedTail_transposeColumn]
    rfl
  simp only [hCol]
  ring

/-- With the retained factors included, the ordinary and alternate Godement tail
kernels have absolutely convergent integrals related by the triangular exchange. -/
def ComplexGapTailExchangeStatement : Prop :=
  ∀ (a : ℂˣ) (T : SplitTailTest k q) (ds : List ComplexCharacterData)
    (W : complexWhittakerModel (k + q) ds (-a)) (χ : ℂˣ →* ℂ) (g h : H) (B : G),
    let μ := complexSelfDualMeasure a
    let ν := entryHaar μ (q + 1)
    let ξ := (rectangularMeasure μ k q).prod ν
    let F := ordinaryBlockTailKernel k q T W.val χ g h B
    let Fd := alternateBlockTailKernel k q a T W.val χ g h B
    Integrable F ξ ∧ Integrable Fd ν ∧
      (∫ p, F p ∂ξ) = (((complexNormalizedAbs B.val.det)⁻¹ : ℝ) : ℂ) ^ q * ∫ z, Fd z ∂ν

theorem complexGapTailExchange : ComplexGapTailExchangeStatement k q := by
  intro a T ds W χ g h B μ ν ξ F Fd
  have hF := funext (ordinaryKernel_eq k q a T ds W χ g h B)
  have hFd := funext (alternateKernel_eq k q a T ds W χ g h B)
  obtain ⟨hI, hId, hIntegral⟩ := complexGapTriangularFourier k q a B T.later
  change Integrable (ordinaryBlockTailKernel k q T W.val χ g h B) ξ ∧
    Integrable (alternateBlockTailKernel k q a T W.val χ g h B) ν ∧
      (∫ p, ordinaryBlockTailKernel k q T W.val χ g h B p ∂ξ) =
        _ * ∫ z, alternateBlockTailKernel k q a T W.val χ g h B z ∂ν
  rw [hF, hFd]
  refine ⟨hI.const_mul _, hId.const_mul _, ?_⟩
  rw [integral_const_mul, integral_const_mul, hIntegral]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapTailExchange
