import Langlands.Global.RankinSelberg.ComplexGapAlternateRepresentative
import Langlands.Global.RankinSelberg.ComplexGapInverseTransposeTailBound
import Langlands.Global.RankinSelberg.ComplexGapOrdinaryMajorant

/-! # Consecutive coordinates for the sparse alternate chart -/

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateCoordinates

open Langlands.GeneralLinear (rankInclusion blockSum_apply_left blockSum_apply_right_left)
open ComplexGapAlternateRepresentative (sparseTailMatrix)
open ComplexGapInverseTransposeTailBound (inverseTailColumns)
open ComplexGapLeadingSchwartz (leadingStack)
open ComplexGapOrdinaryMajorant (leadingInput)
open ComplexGapRightChart (groupCongr rectangleCongr tailSize rightTail_eq_consecutive)
open ComplexGapTailEndpoints (firstTailColumn)
open ComplexGapTriangularChart (Outer)
open ComplexGapUpperTail (firstRectangle)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexTwoBlockHaar (rightTail tailBlockIndex)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ

local instance gapCoordNMeasurable (m : ℕ) : MeasurableSpace (N m) := borel _

/-- Transport logarithms along equality of the lengths of their coordinate vectors. -/
def logCongr {m n : ℕ} (e : m = n) : (Fin m → ℝ) ≃ᵐ (Fin n → ℝ) := by
  subst n
  exact MeasurableEquiv.refl _

/-- Transport the tail unipotent along equality of the two ranks. -/
def unipotentCongr {m n : ℕ} (e : m = n) : N m ≃ᵐ N n := by
  subst n
  exact MeasurableEquiv.refl _

private theorem transport_logTorus_mul {m n : ℕ} (e : m = n) (y : Fin m → ℝ) (Z : N m) :
    logTorus (logCongr e y) * (unipotentCongr e Z).val =
      groupCongr e (logTorus y * Z.val) := by
  subst n
  rfl

private theorem rectangleCongr_apply {k m n : ℕ} (e : m = n) (Y : M k m) (i : Fin k) (j : Fin m) :
    rectangleCongr k e Y i (finCongr e j) = Y i j := by
  subst n
  rfl

variable (k q : ℕ)

local notation "Size" => (k + q + 1)
local notation "TailSize" => (q + 1)
local notation "d" => (k + q + 1 - k)
local notation "e" => (tailSize k q)

private theorem firstRectangle_congr (x : Fin k → ℂ) :
    rectangleCongr k e (firstRectangle k q x) = fun i j => if j.val = 0 then x i else 0 := by
  ext i j
  obtain ⟨j, rfl⟩ := (finCongr e).surjective j
  rw [rectangleCongr_apply]
  change firstRectangle k q x i j = if (j : ℕ) = 0 then x i else 0
  refine Fin.cases ?_ (fun j' => ?_) j <;> simp [firstRectangle]

/-- The sparse chart is the right-tail factor used by the absolute estimates. -/
def ComplexGapAlternateCoordinatesStatement : Prop :=
  ∀ (hk : 0 < k) (hkn : k < Size) (p : Outer k q) (Z : N TailSize),
    sparseTailMatrix k q p Z =
      rightTail hk hkn (logTorus (logCongr e p.1.1.2) * (unipotentCongr e Z).val)
        (fun i j => if j.val = 0 then p.2 i else 0) p.1.2

theorem complexGapAlternateCoordinates : ComplexGapAlternateCoordinatesStatement k q := by
  intro hk hkn p Z
  rw [transport_logTorus_mul, ← firstRectangle_congr k q, rightTail_eq_consecutive]
  rfl

/-- The first physical tail column is unchanged under consecutive indexing. -/
theorem firstTailColumn_consecutive (hk : 0 < k) (hkn : k < Size) (B : G Size) :
    firstTailColumn hk hkn B = fun i => B.val i ((0 : Fin TailSize).natAdd k) := by
  unfold firstTailColumn
  congr 1

/-- The full trailing inverse-transpose block is transported by column reindexing. -/
theorem inverseTailColumns_consecutive (hkn : k < Size) (B : G Size) (i : Fin Size) (j : Fin TailSize) :
    inverseTailColumns hkn B i (finCongr e j) = B⁻¹.val (j.natAdd k) i := by
  have hj : tailBlockIndex hkn (Sum.inr (finCongr e j)) = j.natAdd k := Fin.ext rfl
  simp only [inverseTailColumns, hj]

private theorem leadingInput_zero_congr {a b c : ℕ} (e₀ : b = c) (h : a + c = a + b) (A : M a a) :
    leadingInput h A (0 : M c a) = leadingStack A (0 : M b a) := by
  subst c
  rfl

/-- The leading test matrix in the sparse chart is the stacked matrix with zero lower block. -/
theorem leadingColumns_consecutive (hkn : k < Size) (B : G Size) (g : G k) :
    (fun i j => (B * rankInclusion TailSize g).val i (j.castAdd TailSize)) =
      B.val * leadingInput (Nat.add_sub_of_le hkn.le) g.val (0 : M d k) := by
  rw [leadingInput_zero_congr e]
  have hA : (fun i j => (rankInclusion TailSize g).val i (j.castAdd TailSize)) =
      leadingStack g.val (0 : M TailSize k) := by
    ext i j
    refine Fin.addCases (m := k) (n := TailSize) (fun i₀ => ?_) (fun i₁ => ?_) i
    · change (Langlands.GeneralLinear.blockSum (g, (1 : G TailSize))).val
        (i₀.castAdd TailSize) (j.castAdd TailSize) = _
      rw [blockSum_apply_left]
      simp only [leadingStack, Fin.append_left]
    · change (Langlands.GeneralLinear.blockSum (g, (1 : G TailSize))).val
        (i₁.natAdd k) (j.castAdd TailSize) = _
      rw [blockSum_apply_right_left]
      simp only [leadingStack, Fin.append_right, Matrix.zero_apply]
  rw [← hA]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateCoordinates
