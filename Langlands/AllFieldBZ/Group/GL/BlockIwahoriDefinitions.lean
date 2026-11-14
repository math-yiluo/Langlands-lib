import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.Group.GL.BlockIwahoriDefinitions

/-!
# All-field port of `Langlands.Group.GL.BlockIwahoriDefinitions`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockIwahoriDefinitions` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped NNReal
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe u

variable {n : ℕ} (B : GeneralLinear.BlockShape n) (R : Type u) [CommRing R]

variable (K : Subgroup (GeneralLinear n R))

section Padic
variable {F : LocalFieldPackage.{u}} (T : F.TopologicalData)

/-- The actual root-ratio character in block-scalar coordinates. -/
def _root_.Langlands.GeneralLinear.BlockShape.blockScalarRatio_allFieldBZ (i j : Fin B.length) : (Fin B.length → F.Carrierˣ) →* ℝ≥0ˣ where
  toFun a := T.normalizedAbsUnits (a i * (a j)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    simp only [Pi.mul_apply, mul_inv_rev]
    rw [show a i * b i * ((b j)⁻¹ * (a j)⁻¹) =
      (a i * (a j)⁻¹) * (b i * (b j)⁻¹) by ac_rfl, map_mul]

@[simp] theorem _root_.Langlands.GeneralLinear.BlockShape.blockScalarRatio_apply_allFieldBZ (a : Fin B.length → F.Carrierˣ)
    (i j : Fin B.length) :
    B.blockScalarRatio_allFieldBZ T i j a = T.normalizedAbsUnits (a i * (a j)⁻¹) := rfl

/-- Weak contraction of the upper radical: every forward block ratio is at most one. -/
def _root_.Langlands.GeneralLinear.BlockShape.IsWeaklyContracting_allFieldBZ (a : Fin B.length → F.Carrierˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → (((B.blockScalarRatio_allFieldBZ T i j a : ℝ≥0) : ℝ) ≤ 1)

/-- Strict contraction of the upper radical: every forward block ratio is below one. -/
def _root_.Langlands.GeneralLinear.BlockShape.IsStrictlyContracting_allFieldBZ (a : Fin B.length → F.Carrierˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → (((B.blockScalarRatio_allFieldBZ T i j a : ℝ≥0) : ℝ) < 1)

/-- The ratio inequalities alone; consumers separately impose `0 < ε` and `ε ≤ 1`. -/
def _root_.Langlands.GeneralLinear.BlockShape.IsDeeplyContracting_allFieldBZ (ε : ℝ) (a : Fin B.length → F.Carrierˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → (((B.blockScalarRatio_allFieldBZ T i j a : ℝ≥0) : ℝ) < ε)

@[simp] theorem _root_.Langlands.GeneralLinear.BlockShape.isWeaklyContracting_one_allFieldBZ : B.IsWeaklyContracting_allFieldBZ T 1 := by
  intro i j _
  simp

theorem _root_.Langlands.GeneralLinear.BlockShape.IsStrictlyContracting_allFieldBZ.weak {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsStrictlyContracting_allFieldBZ T a) : B.IsWeaklyContracting_allFieldBZ T a :=
  fun i j hij => (ha i j hij).le

theorem _root_.Langlands.GeneralLinear.BlockShape.IsDeeplyContracting_allFieldBZ.strict {ε : ℝ} {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsDeeplyContracting_allFieldBZ T ε a) (hε : ε ≤ 1) : B.IsStrictlyContracting_allFieldBZ T a :=
  fun i j hij => (ha i j hij).trans_le hε

theorem _root_.Langlands.GeneralLinear.BlockShape.IsWeaklyContracting_allFieldBZ.mul {a b : Fin B.length → F.Carrierˣ}
    (ha : B.IsWeaklyContracting_allFieldBZ T a) (hb : B.IsWeaklyContracting_allFieldBZ T b) :
    B.IsWeaklyContracting_allFieldBZ T (a * b) := by
  intro i j hij
  rw [map_mul, Units.val_mul, NNReal.coe_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (ha i j hij) (hb i j hij) (by positivity) zero_le_one
    _ = 1 := one_mul 1

/-- A weak-chamber version of block Iwahori factorization for an actual open subgroup.
Compactness is deliberately a separate `IsCompact (K : Set _)` hypothesis. -/
def _root_.Langlands.GeneralLinear.BlockShape.HasBlockIwahoriFactorization_allFieldBZ :
    letI := T.topology
    OpenSubgroup (GeneralLinear n F.Carrier) → Prop :=
  letI := T.topology
  fun K =>
    Function.Bijective (B.iwahoriProduct F.Carrier K.toSubgroup) ∧
    ∀ a : Fin B.length → F.Carrierˣ, B.IsWeaklyContracting_allFieldBZ T a →
      (∀ g ∈ B.iwahoriUpper F.Carrier K.toSubgroup,
        B.blockScalar F.Carrier a * g * (B.blockScalar F.Carrier a)⁻¹ ∈
          B.iwahoriUpper F.Carrier K.toSubgroup) ∧
      (∀ g ∈ B.iwahoriLower F.Carrier K.toSubgroup,
        (B.blockScalar F.Carrier a)⁻¹ * g * B.blockScalar F.Carrier a ∈
          B.iwahoriLower F.Carrier K.toSubgroup)

theorem _root_.Langlands.GeneralLinear.BlockShape.HasBlockIwahoriFactorization_allFieldBZ.bijective :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)},
      B.HasBlockIwahoriFactorization_allFieldBZ T K →
        Function.Bijective (B.iwahoriProduct F.Carrier K.toSubgroup) := by
  let := T.topology
  intro K hK
  exact hK.1

end Padic
end Langlands.AllFieldBZ.GeneralLinear.BlockShape
