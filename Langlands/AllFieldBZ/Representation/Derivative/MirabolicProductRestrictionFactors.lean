import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Group.GL.MirabolicModularCharacterProof
import Langlands.AllFieldBZ.Representation.Derivative.MinusVanishing
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.MirabolicProductRestrictionFactors

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductRestrictionFactors`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductRestrictionFactors` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped TensorProduct
open scoped NNReal
namespace Langlands.AllFieldBZ
universe uR uG uV uW uF

namespace FiniteTensor
open Langlands.FiniteTensor
section Binary
variable (R : Type uR) [CommRing R]
variable (V : Fin 2 → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

variable {R V}

end Binary
end FiniteTensor
namespace Derivative.MirabolicProductRestriction
open Langlands.Derivative.MirabolicProductRestriction hiding determinantNorm_mirabolic leviHalfModulus_eq_leftLeviCharacter leviHalfModulus_eq_rightLeviCharacter leviModulus_shape
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
section Characters
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) (m n : ℕ)

theorem determinantNorm_mirabolic {r : ℕ} (g : mirabolic r F.Carrier) :
    T.determinantNorm (r + 1) g.val = T.determinantNorm r (Mirabolic.projection g) := by
  change T.normalizedAbsUnits (GeneralLinear.determinant g.val) =
    T.normalizedAbsUnits (GeneralLinear.determinant (Mirabolic.projection g))
  rw [GeneralLinear.Mirabolic.determinant_projection]

/-- The binary block modulus `ν(m₀)^(n+1) / ν(m₁)^(m+1)`. -/
theorem leviModulus_shape (x : (shape m n).Levi F.Carrier) :
    T.leviModulus (shape m n) x =
      T.determinantNorm (m + 1) (x (0 : Fin 2)) ^ (n + 1) /
        T.determinantNorm (n + 1) (x (1 : Fin 2)) ^ (m + 1) := by
  rw [LocalFieldPackage.TopologicalData.leviModulus_apply]
  change ∏ i : Fin 2, ∏ j ∈ Finset.univ.filter (fun j : Fin 2 => i < j),
      T.determinantNorm ((shape m n).size i) (x i) ^ (shape m n).size j /
        T.determinantNorm ((shape m n).size j) (x j) ^ (shape m n).size i = _
  rw [Fin.prod_univ_two]
  have h0 : Finset.univ.filter (fun j : Fin 2 => (0 : Fin 2) < j) = {1} := by decide
  have h1 : Finset.univ.filter (fun j : Fin 2 => (1 : Fin 2) < j) = ∅ := by decide
  rw [h0, h1, Finset.prod_singleton, Finset.prod_empty, mul_one]
  rfl

private theorem _root_.Langlands.Derivative.MirabolicProductRestriction.sqrt_div_pow (x y : ℝ≥0ˣ) (a b : ℕ) :
    ((NNReal.sqrt ((x ^ a / y ^ b : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) =
      ((((x : ℝ≥0) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-((b : ℝ) / 2)) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  have hx : (0 : ℝ) < ((x : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt x)
  have hy : (0 : ℝ) < ((y : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt y)
  rw [Real.coe_sqrt, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow,
    Real.sqrt_eq_rpow, Real.div_rpow (pow_nonneg hx.le _) (pow_nonneg hy.le _),
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le,
    div_eq_mul_inv _ (((y : ℝ≥0) : ℝ) ^ ((b : ℝ) * (1 / 2))), ← Real.rpow_neg hy.le]
  congr 1 <;> congr 1 <;> ring

/-- Case (II): on the closed-orbit stabilizer `δ^(1/2)` is `χ_L`. -/
theorem leviHalfModulus_eq_leftLeviCharacter (x : (shape m n).Levi F.Carrier)
    (q : mirabolic n F.Carrier) (hq : x (1 : Fin 2) = q.val) :
    (T.leviHalfModulus (shape m n) x : ℂ) = T.leftLeviCharacter (m + 1) n (x (0 : Fin 2), q) := by
  rw [LocalFieldPackage.TopologicalData.leviHalfModulus_apply, leviModulus_shape,
    LocalFieldPackage.TopologicalData.leftLeviCharacter_apply, sqrt_div_pow, hq]

/-- Case (III): on the open-orbit stabilizer `δ^(1/2)` is `χ_R`, including the
retained factor `ε`. -/
theorem leviHalfModulus_eq_rightLeviCharacter (x : (shape m n).Levi F.Carrier)
    (q : mirabolic m F.Carrier) (hq : x (0 : Fin 2) = q.val) :
    (T.leviHalfModulus (shape m n) x : ℂ) = T.rightLeviCharacter (n + 1) m (q, x (1 : Fin 2)) := by
  rw [LocalFieldPackage.TopologicalData.leviHalfModulus_apply, leviModulus_shape,
    LocalFieldPackage.TopologicalData.rightLeviCharacter_apply, sqrt_div_pow, hq,
    determinantNorm_mirabolic]

end Characters
end Derivative.MirabolicProductRestriction
end Langlands.AllFieldBZ
