import Langlands.LocalFactor.Archimedean.Definitions
import Langlands.Weil.ArchimedeanRepresentation

/-!
# Arithmetic factors of explicitly presented archimedean Weil blocks

Character parameters are certified by equations for actual continuous characters.
The associated representations are the published line and induction constructions.
No classification or presentation-independence theorem is assumed.
-/

noncomputable section

namespace Langlands.LocalFactor.Archimedean

open Langlands.Weil.Archimedean

/-- Parameters for an actual real character. The equation fixes the polar convention;
it is not an assumption about arithmetic factors. -/
structure RealCharacterData where
  character : ℝˣ →ₜ* ℂˣ
  parity : Fin 2
  exponent : ℂ
  character_eq : ∀ x : ℝˣ, (character x : ℂ) =
    (((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ) ^ parity.val *
      ((|(x : ℝ)| : ℝ) : ℂ) ^ exponent

/-- Parameters for an actual complex character. The norm here is Euclidean;
its square is the normalized local absolute value. -/
structure ComplexCharacterData where
  character : ComplexWeil →ₜ* ℂˣ
  weight : ℤ
  exponent : ℂ
  character_eq : ∀ z : ComplexWeil, (character z : ℂ) =
    ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ weight *
      (‖(z : ℂ)‖ : ℂ) ^ (2 * exponent)

namespace RealCharacterData

/-- The actual representation on the complex line, pulled back along the
published real abelian coordinate. -/
def representation (d : RealCharacterData) :
    FiniteRepresentation.ContinuousObjects RealWeil :=
  realCharacter d.character

@[simp]
theorem representation_rank (d : RealCharacterData) :
    d.representation.val.rank = 1 := realCharacter_rank _

theorem representation_apply (d : RealCharacterData) (w : RealWeil) (v : ℂ) :
    d.representation.val.representation w v =
      ((((RealWeil.abelianCoordinate w : ℝ) /
          |(RealWeil.abelianCoordinate w : ℝ)| : ℝ) : ℂ) ^ d.parity.val *
        ((|(RealWeil.abelianCoordinate w : ℝ)| : ℝ) : ℂ) ^ d.exponent) * v := by
  change (d.character (RealWeil.abelianCoordinate w) : ℂ) * v = _
  rw [d.character_eq]

/-- The spectral L-factor of this presented real character. -/
def lFactor (d : RealCharacterData) : ReciprocalEntire :=
  realTateL d.parity (d.exponent + (d.parity.val : ℂ))

/-- Standard plus-character epsilon, for Lebesgue measure on the real field. -/
def standardEpsilon (d : RealCharacterData) : ℂˣ :=
  Units.mk0 (realTateEpsilon d.parity) (realTateEpsilon_ne_zero _)

@[simp]
theorem coe_standardEpsilon (d : RealCharacterData) :
    (d.standardEpsilon : ℂ) = Complex.I ^ d.parity.val := rfl

theorem lFactor_isPole (d : RealCharacterData) (s : ℂ) :
    d.lFactor.IsPole s ↔
      ∃ n : ℕ, s + (d.exponent + (d.parity.val : ℂ)) = -(2 * (n : ℂ)) :=
  gammaReal_isPole _

theorem lFactor_eval (d : RealCharacterData) (s : d.lFactor.RegularPoint) :
    (d.lFactor.eval s : ℂ) =
      (Real.pi : ℂ) ^ (-(s.val + (d.exponent + (d.parity.val : ℂ))) / 2) *
        Complex.Gamma ((s.val + (d.exponent + (d.parity.val : ℂ))) / 2) :=
  gammaReal_eval ⟨_, s.property⟩

/-- A concrete weight-zero input, requiring no character-classification theorem. -/
def trivial : RealCharacterData where
  character := 1
  parity := 0
  exponent := 0
  character_eq := by intro x; simp

end RealCharacterData

namespace ComplexCharacterData

/-- The actual complex Weil representation on the complex line. -/
def representation (d : ComplexCharacterData) :
    FiniteRepresentation.ContinuousObjects ComplexWeil :=
  complexCharacter d.character

@[simp]
theorem representation_rank (d : ComplexCharacterData) :
    d.representation.val.rank = 1 := complexCharacter_rank _

theorem representation_apply (d : ComplexCharacterData) (z : ComplexWeil) (v : ℂ) :
    d.representation.val.representation z v =
      (((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ d.weight *
        (‖(z : ℂ)‖ : ℂ) ^ (2 * d.exponent)) * v := by
  change (d.character z : ℂ) * v = _
  rw [d.character_eq]

/-- The spectral L-factor of this presented complex character. -/
def lFactor (d : ComplexCharacterData) : ReciprocalEntire :=
  complexTateL d.weight.natAbs (d.exponent + (d.weight.natAbs : ℂ) / 2)

/-- Standard trace-character epsilon, for twice Euclidean area on the complex field. -/
def standardEpsilon (d : ComplexCharacterData) : ℂˣ :=
  Units.mk0 (complexTateEpsilon d.weight.natAbs) (complexTateEpsilon_ne_zero _)

@[simp]
theorem coe_standardEpsilon (d : ComplexCharacterData) :
    (d.standardEpsilon : ℂ) = Complex.I ^ d.weight.natAbs := rfl

theorem lFactor_isPole (d : ComplexCharacterData) (s : ℂ) :
    d.lFactor.IsPole s ↔
      ∃ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) = -(n : ℂ) :=
  gammaComplex_isPole _

theorem lFactor_eval (d : ComplexCharacterData) (s : d.lFactor.RegularPoint) :
    (d.lFactor.eval s : ℂ) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(s.val +
        (d.exponent + (d.weight.natAbs : ℂ) / 2))) *
        Complex.Gamma (s.val + (d.exponent + (d.weight.natAbs : ℂ) / 2)) :=
  gammaComplex_eval ⟨_, s.property⟩

/-- The actual two-dimensional induction model over the real Weil group.
Weight zero is allowed and is not asserted irreducible. -/
def realInducedRepresentation (d : ComplexCharacterData) :
    FiniteRepresentation.ContinuousObjects RealWeil :=
  realInducedCharacter d.character

@[simp]
theorem realInducedRepresentation_rank (d : ComplexCharacterData) :
    d.realInducedRepresentation.val.rank = 2 := realInducedCharacter_rank _

theorem realInducedRepresentation_ofComplex (d : ComplexCharacterData)
    (z : ComplexWeil) (v : ℂ × ℂ) :
    d.realInducedRepresentation.val.representation (RealWeil.ofComplex z) v =
      ((d.character z : ℂ) * v.1, (d.character (star z) : ℂ) * v.2) :=
  twoDimensionalAction_ofComplex _ _ _

theorem realInducedRepresentation_j (d : ComplexCharacterData) (v : ℂ × ℂ) :
    d.realInducedRepresentation.val.representation RealWeil.j v =
      (v.2, (d.character (-1) : ℂ) * v.1) :=
  twoDimensionalAction_j _ _

/-- Induction uses the complex L-factor with its actual parameter shift. -/
def realInducedLFactor (d : ComplexCharacterData) : ReciprocalEntire := d.lFactor

/-- The complex-to-real induction correction for the standard plus character. -/
def realInducedStandardEpsilon (d : ComplexCharacterData) : ℂˣ :=
  Units.mk0 (Complex.I ^ (d.weight.natAbs + 1)) (pow_ne_zero _ Complex.I_ne_zero)

@[simp]
theorem coe_realInducedStandardEpsilon (d : ComplexCharacterData) :
    (d.realInducedStandardEpsilon : ℂ) = Complex.I ^ (d.weight.natAbs + 1) := rfl

/-- The induction correction is retained separately from the complex phase. -/
theorem realInducedStandardEpsilon_eq (d : ComplexCharacterData) :
    d.realInducedStandardEpsilon =
      d.standardEpsilon * Units.mk0 Complex.I Complex.I_ne_zero := by
  apply Units.ext
  exact pow_succ _ _

theorem realInducedLFactor_isPole (d : ComplexCharacterData) (s : ℂ) :
    d.realInducedLFactor.IsPole s ↔
      ∃ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) = -(n : ℂ) :=
  d.lFactor_isPole s

/-- The trivial character is also a valid induced input. -/
def trivial : ComplexCharacterData where
  character := 1
  weight := 0
  exponent := 0
  character_eq := by intro z; simp

@[simp]
theorem trivial_realInducedStandardEpsilon :
    (trivial.realInducedStandardEpsilon : ℂ) = Complex.I := by
  simp [trivial]

end ComplexCharacterData

end Langlands.LocalFactor.Archimedean
