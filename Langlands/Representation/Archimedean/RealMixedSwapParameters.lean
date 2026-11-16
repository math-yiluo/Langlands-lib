import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-!
# Parameters for signed reversal of mixed real blocks

The inverse-reversed induction datum keeps its weight and negates its exponent.
The real character also acquires the determinant-sign parity of the induction block.
-/

noncomputable section

namespace Langlands.Archimedean.RealMixedSwapTwist

open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The sign character on real units, viewed as a complex number. -/
def unitSign (x : ℝˣ) : ℂ := (((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ)

theorem unitSign_sq (x : ℝˣ) : unitSign x ^ 2 = 1 := by
  have h : ((x : ℝ) / |(x : ℝ)|) ^ 2 = 1 := by
    rw [div_pow, sq_abs, div_self (pow_ne_zero 2 x.ne_zero)]
  unfold unitSign
  exact_mod_cast h

theorem unitSign_inv (x : ℝˣ) : unitSign x⁻¹ = unitSign x := by
  unfold unitSign
  rw [Units.val_inv_eq_inv_val, abs_inv, inv_div_inv]
  congr 1
  apply (div_eq_div_iff x.ne_zero (abs_ne_zero.mpr x.ne_zero)).mpr
  rw [← sq, ← sq, sq_abs]

theorem abs_inv_cpow (x : ℝˣ) (c : ℂ) :
    ((|(↑x⁻¹ : ℝ)| : ℝ) : ℂ) ^ c = ((|(x : ℝ)| : ℝ) : ℂ) ^ (-c) := by
  rw [Units.val_inv_eq_inv_val, abs_inv, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (abs_nonneg (x : ℝ))]
      exact Real.pi_ne_zero.symm), Complex.cpow_neg]

/-- The discrete-series datum after inverse reversal. -/
def reverseInduced (d : ComplexCharacterData) : ComplexCharacterData :=
  characterOfParams d.weight (-d.exponent)

/-- The real character after inverse reversal and a determinant-sign power. -/
def signedInverseCharacter (q : ℕ) (b : RealCharacterData) : RealCharacterData :=
  RealJacquetFrobenius.charData ⟨(q + b.parity.val) % 2, Nat.mod_lt _ (by decide)⟩
    (-b.exponent)

/-- The sign power that restores the induction block's first-character convention. -/
def mixedSignPower (d : ComplexCharacterData) : ℕ := d.weight.natAbs + 1

/-- The real character paired with `reverseInduced d` under signed reversal. -/
def reverseCharacter (d : ComplexCharacterData) (b : RealCharacterData) : RealCharacterData :=
  signedInverseCharacter (mixedSignPower d) b

@[simp] theorem reverseInduced_weight (d : ComplexCharacterData) :
    (reverseInduced d).weight = d.weight := rfl

@[simp] theorem reverseInduced_exponent (d : ComplexCharacterData) :
    (reverseInduced d).exponent = -d.exponent := rfl

@[simp] theorem signedInverseCharacter_exponent (q : ℕ) (b : RealCharacterData) :
    (signedInverseCharacter q b).exponent = -b.exponent := rfl

@[simp] theorem reverseCharacter_exponent (d : ComplexCharacterData) (b : RealCharacterData) :
    (reverseCharacter d b).exponent = -b.exponent := rfl

@[simp] theorem reverseCharacter_parity_val (d : ComplexCharacterData) (b : RealCharacterData) :
    (reverseCharacter d b).parity.val = (mixedSignPower d + b.parity.val) % 2 := rfl

theorem signedInverseCharacter_apply (q : ℕ) (b : RealCharacterData) (x : ℝˣ) :
    ((signedInverseCharacter q b).character x : ℂ) =
      unitSign x ^ q * (b.character x⁻¹ : ℂ) := by
  rw [(signedInverseCharacter q b).character_eq, b.character_eq]
  change unitSign x ^ ((q + b.parity.val) % 2) * _ =
    unitSign x ^ q * (unitSign x⁻¹ ^ b.parity.val * _)
  rw [unitSign_inv, abs_inv_cpow, ← pow_eq_pow_mod _ (unitSign_sq x), pow_add,
    signedInverseCharacter_exponent]
  ring

theorem realInducedFirstCharacter_reverse (d : ComplexCharacterData) (x : ℝˣ) :
    realInducedFirstCharacter (reverseInduced d) x =
      unitSign x ^ mixedSignPower d * realInducedSecondCharacter d x⁻¹ := by
  simp only [realInducedFirstCharacter, realInducedSecondCharacter,
    reverseInduced_weight, reverseInduced_exponent, abs_inv_cpow]
  congr 1
  congr 1
  ring

theorem realInducedSecondCharacter_reverse (d : ComplexCharacterData) (x : ℝˣ) :
    realInducedSecondCharacter (reverseInduced d) x =
      unitSign x ^ mixedSignPower d * realInducedFirstCharacter d x⁻¹ := by
  simp only [realInducedFirstCharacter, realInducedSecondCharacter,
    reverseInduced_weight, reverseInduced_exponent]
  change _ = unitSign x ^ mixedSignPower d *
    (unitSign x⁻¹ ^ mixedSignPower d * _)
  rw [unitSign_inv, abs_inv_cpow, ← mul_assoc, ← mul_pow, ← sq, unitSign_sq, one_pow, one_mul]
  congr 1
  ring

/-- All three position characters of an induction-character pair under signed reversal. -/
theorem positionCharacter_induced_character (d : ComplexCharacterData) (b : RealCharacterData)
    (j : Fin 3) (x : ℝˣ) :
    realPositionCharacter [.character (reverseCharacter d b), .induced (reverseInduced d)] j x =
      unitSign x ^ mixedSignPower d *
        realPositionCharacter [.induced d, .character b] (Fin.rev j) x⁻¹ := by
  fin_cases j
  · exact signedInverseCharacter_apply (mixedSignPower d) b x
  · exact realInducedFirstCharacter_reverse d x
  · exact realInducedSecondCharacter_reverse d x

/-- All three position characters of a character-induction pair under signed reversal. -/
theorem positionCharacter_character_induced (d : ComplexCharacterData) (b : RealCharacterData)
    (j : Fin 3) (x : ℝˣ) :
    realPositionCharacter [.induced (reverseInduced d), .character (reverseCharacter d b)] j x =
      unitSign x ^ mixedSignPower d *
        realPositionCharacter [.character b, .induced d] (Fin.rev j) x⁻¹ := by
  fin_cases j
  · exact realInducedFirstCharacter_reverse d x
  · exact realInducedSecondCharacter_reverse d x
  · exact signedInverseCharacter_apply (mixedSignPower d) b x

/-- Signed reversal takes the required exponent order to the opposite mixed order. -/
theorem exponent_order_reverse (d : ComplexCharacterData) (b : RealCharacterData) :
    realBlockExponent (.induced (reverseInduced d)) ≤
      realBlockExponent (.character (reverseCharacter d b)) ↔
        realBlockExponent (.character b) ≤ realBlockExponent (.induced d) := by
  simp [realBlockExponent]

/-- Mixed unlinkedness is unchanged by negating both exponents and reversing the pair.
The character parity does not enter the mixed linkedness condition. -/
theorem unlinked_reverse (d : ComplexCharacterData) (b : RealCharacterData)
    (hw : d.weight ≠ 0) :
    AreRealBlocksUnlinked (.character (reverseCharacter d b)) (.induced (reverseInduced d)) ↔
      AreRealBlocksUnlinked (.induced d) (.character b) := by
  simp only [AreRealBlocksUnlinked, realBlockMoeglinData, reverseInduced_weight,
    reverseInduced_exponent, reverseCharacter_exponent, hw, ↓reduceIte,
    List.mem_singleton, forall_eq, MoeglinDatum.IsLinked, neg_sub_neg]
  simp only [or_comm]

end Langlands.Archimedean.RealMixedSwapTwist
