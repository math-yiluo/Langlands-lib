import Langlands.Representation.Shahidi.Induction
import Langlands.AllField.Group.GL.UnramifiedCharacterSupplement
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Shahidi.TwoBlocks
/-!
# Shahidi's two-block induced representations `I(s, π₁ ⊗ π₂)` and `I(-s, π₂ ⊗ π₁)`

For positive ranks `m, n`, a complex number `s` and representations `π₁` of `GL_m(F)`
and `π₂` of `GL_n(F)`, Shahidi (1984, printed pages 67 and 72) induces
`π₁ |det|^(s/2) ⊗ π₂ |det|^(-s/2)` from the standard upper parabolic of `GL_(m+n)(F)`
with Levi `GL_m × GL_n`, and compares it with the induction `I(-s, π₂ ⊗ π₁)` from the
parabolic with Levi `GL_n × GL_m`.

Both representations are the published normalized block induction
`BlockShape.productInducedOf` (respectively `TopologicalData.normalizedProductInduced`)
of a block tensor product of determinant twists. The normalizing character is the
positive square root of the explicit block modulus `|det m₁|^n / |det m₂|^m`. The
resulting covariance exponents are `(s + n)/2` and `-(s + m)/2` for the original order
and `(m - s)/2` and `(s - n)/2` for the swapped order.

The general layer works over any field with a topology and a real absolute value whose
norm-one units form an open set; for a non-archimedean local field this holds when the
absolute value is trivial on valuation units. The p-adic layer feeds the unit
`q^(-t) = exp(-t log q)` to the Library's unramified determinant characters.
-/

noncomputable section

open scoped NNReal

namespace Langlands.AllField.Shahidi
open Langlands.Shahidi
open Langlands.AllField.Shahidi

universe uH uF uV uR

open Langlands.GeneralLinear

/-! ## Complex powers of positive characters -/

section ComplexPower


end ComplexPower

/-! ## Absolute values and determinant powers -/

section AbsoluteValue




end AbsoluteValue

/-! ## The explicit block modulus for an absolute value -/

section Modulus



end Modulus

/-! ## The swapped two-block shape -/

section Shapes



end Shapes

/-! ## Two-factor carriers and families -/

section Pair






end Pair

/-! ## The swapped shape and `swapRank` -/

section SwapRank


end SwapRank

/-! ## Determinant twists of a pair -/

section Twists


end Twists

/-! ## The general two-block induction -/

section Induction


end Induction

end Langlands.AllField.Shahidi

/-! ## The p-adic specialization -/

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.Shahidi hiding isOpen_ker_leviHalfModulus isOpen_ker_leviModulus leviHalfCharacter leviHalfCharacter_toMonoidHom leviHalfModulus leviHalfModulus_apply leviHalfModulus_eq_one leviModulus leviModulus_apply leviModulus_swappedTwoBlocks leviModulus_twoBlocks
open Langlands.AllField.Shahidi
open Langlands.GeneralLinear hiding blockSum rankInclusion

universe uF uV

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The residue cardinality `q`, as a positive real number. -/
theorem residueCardinality_real_pos : (0 : ℝ) < T.residueCardinality := by
  exact_mod_cast Nat.zero_lt_one.trans T.residueCardinality_gt_one

/-! ### Comparison of the general layer with the normalized absolute value -/

section Comparison

variable {T} {abv : AbsoluteValue F ℝ} (habv : ∀ x, abv x = T.normalizedAbs x)
include habv

theorem absUnits_eq_normalizedAbsUnits : absUnits abv = T.normalizedAbsUnits := by
  ext u
  exact habv u

/-- The normalized absolute value satisfies the smoothness hypothesis of the general
layer. -/
theorem isOpenNormOne_of_eq_normalizedAbs :
    letI := T.topology
    IsOpenNormOne abv := by
  let := T.topology
  change IsOpen ((absUnits abv).ker : Set Fˣ)
  rw [absUnits_eq_normalizedAbsUnits habv]
  exact T.isOpen_ker_normalizedAbsUnits

end Comparison

/-! ### Complex determinant powers through unramified characters -/

/-- `g ↦ |det g|^t` for every complex `t`: the Library's unramified determinant character
at the nonzero complex number `q^(-t) = exp(-t log q)`. -/
def determinantComplexPower (n : ℕ) (t : ℂ) : GeneralLinear n F →* ℂˣ :=
  T.determinantUnramifiedCharacter n
    (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos t)

/-- The unramified parametrization agrees with the complex power of the positive
normalized determinant absolute value. -/
theorem determinantComplexPower_apply (n : ℕ) (t : ℂ) (g : GeneralLinear n F) :
    (T.determinantComplexPower n t g : ℂ) = (((T.determinantNorm n g : ℝ≥0) : ℝ) : ℂ) ^ t := by
  have hq : (0 : ℝ) < T.residueCardinality := T.residueCardinality_real_pos
  have hpos : (0 : ℝ) < (T.residueCardinality : ℝ) ^
      (-T.ord (GeneralLinear.determinant g : F)) := zpow_pos hq _
  rw [determinantComplexPower, T.determinantUnramifiedCharacter_apply, Units.val_zpow_eq_zpow_val,
    T.determinantNorm_eq_residue_pow,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
    ← Complex.ofReal_log hpos.le, Real.log_zpow]
  change Complex.exp (-t * (Real.log T.residueCardinality : ℂ)) ^ _ = _
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem determinantComplexPower_eq_complexPower (n : ℕ) (t : ℂ) :
    T.determinantComplexPower n t = complexPower (T.determinantNorm n) t := by
  ext g
  exact T.determinantComplexPower_apply n t g

theorem determinantComplexPower_add (n : ℕ) (s t : ℂ) :
    T.determinantComplexPower n (s + t) =
      T.determinantComplexPower n s * T.determinantComplexPower n t := by
  simp only [determinantComplexPower_eq_complexPower, complexPower_add]

theorem determinantComplexPower_neg (n : ℕ) (t : ℂ) :
    T.determinantComplexPower n (-t) = (T.determinantComplexPower n t)⁻¹ := by
  simp only [determinantComplexPower_eq_complexPower, complexPower_neg]

@[simp]
theorem determinantComplexPower_zero (n : ℕ) : T.determinantComplexPower n 0 = 1 := by
  simp only [determinantComplexPower_eq_complexPower, complexPower_zero]

theorem isOpen_ker_determinantComplexPower (n : ℕ) (t : ℂ) :
    letI := T.topology
    IsOpen ((T.determinantComplexPower n t).ker : Set (GeneralLinear n F)) :=
  T.isOpen_ker_determinantUnramifiedCharacter n _

/-! ### The p-adic induced representations -/


end Langlands.LocalFieldData

/-! ## Canonical aliases -/

namespace Langlands

open Langlands.Shahidi
open Langlands.AllField.Shahidi
open Langlands.GeneralLinear

universe uF uV


end Langlands
