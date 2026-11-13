import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.AllField.Group.GL.NormalizedCharacter
noncomputable section

open scoped NNReal

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape hiding HasBlockIwahoriFactorization IsDeeplyContracting IsStrictlyContracting IsWeaklyContracting blockScalarRatio blockScalarRatio_apply isWeaklyContracting_one
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe u

variable {n : ℕ} (B : GeneralLinear.BlockShape n) (R : Type u) [CommRing R]

variable (K : Subgroup (GeneralLinear n R))

section Padic

variable {F : Type u} [Field F] (T : LocalFieldData F)

/-- The actual root-ratio character in block-scalar coordinates. -/
def blockScalarRatio (i j : Fin B.length) : (Fin B.length → Fˣ) →* ℝ≥0ˣ where
  toFun a := T.normalizedAbsUnits (a i * (a j)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    simp only [Pi.mul_apply, mul_inv_rev]
    rw [show a i * b i * ((b j)⁻¹ * (a j)⁻¹) =
      (a i * (a j)⁻¹) * (b i * (b j)⁻¹) by ac_rfl, map_mul]

@[simp] theorem blockScalarRatio_apply (a : Fin B.length → Fˣ)
    (i j : Fin B.length) :
    (Langlands.AllField.GeneralLinear.BlockShape.blockScalarRatio B) T i j a = T.normalizedAbsUnits (a i * (a j)⁻¹) := rfl

/-- Weak contraction of the upper radical: every forward block ratio is at most one. -/
def IsWeaklyContracting (a : Fin B.length → Fˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → ((((Langlands.AllField.GeneralLinear.BlockShape.blockScalarRatio B) T i j a : ℝ≥0) : ℝ) ≤ 1)

/-- Strict contraction of the upper radical: every forward block ratio is below one. -/
def IsStrictlyContracting (a : Fin B.length → Fˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → ((((Langlands.AllField.GeneralLinear.BlockShape.blockScalarRatio B) T i j a : ℝ≥0) : ℝ) < 1)

/-- The ratio inequalities alone; consumers separately impose `0 < ε` and `ε ≤ 1`. -/
def IsDeeplyContracting (ε : ℝ) (a : Fin B.length → Fˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → ((((Langlands.AllField.GeneralLinear.BlockShape.blockScalarRatio B) T i j a : ℝ≥0) : ℝ) < ε)

@[simp] theorem isWeaklyContracting_one : (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T 1 := by
  intro i j _
  simp

theorem IsStrictlyContracting.weak {a : Fin B.length → Fˣ}
    (ha : (Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting B) T a) : (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a :=
  fun i j hij => (ha i j hij).le

theorem IsDeeplyContracting.strict {ε : ℝ} {a : Fin B.length → Fˣ}
    (ha : (Langlands.AllField.GeneralLinear.BlockShape.IsDeeplyContracting B) T ε a) (hε : ε ≤ 1) : (Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting B) T a :=
  fun i j hij => (ha i j hij).trans_le hε

theorem IsWeaklyContracting.mul {a b : Fin B.length → Fˣ}
    (ha : (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a) (hb : (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T b) :
    (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T (a * b) := by
  intro i j hij
  rw [map_mul, Units.val_mul, NNReal.coe_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (ha i j hij) (hb i j hij) (by positivity) zero_le_one
    _ = 1 := one_mul 1

/-- A weak-chamber version of block Iwahori factorization for an actual open subgroup.
Compactness is deliberately a separate `IsCompact (K : Set _)` hypothesis. -/
def HasBlockIwahoriFactorization :
    letI := T.topology
    OpenSubgroup (GeneralLinear n F) → Prop :=
  letI := T.topology
  fun K =>
    Function.Bijective (B.iwahoriProduct F K.toSubgroup) ∧
    ∀ a : Fin B.length → Fˣ, (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a →
      (∀ g ∈ B.iwahoriUpper F K.toSubgroup,
        B.blockScalar F a * g * (B.blockScalar F a)⁻¹ ∈
          B.iwahoriUpper F K.toSubgroup) ∧
      (∀ g ∈ B.iwahoriLower F K.toSubgroup,
        (B.blockScalar F a)⁻¹ * g * B.blockScalar F a ∈
          B.iwahoriLower F K.toSubgroup)

end Padic
end Langlands.AllField.GeneralLinear.BlockShape
