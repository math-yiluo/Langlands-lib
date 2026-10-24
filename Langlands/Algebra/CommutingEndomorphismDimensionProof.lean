import Langlands.Algebra.CommutingEndomorphismDimensionStatement
import Langlands.Algebra.CommutingDimensionPrimary
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Proof of the natural-power commuting endomorphism dimension bound over `ℂ`. -/

namespace Langlands

universe uV

/-- BZ76 Lemma 4.10 in natural-power form, obtained by specializing the
general algebraically closed field theorem to `ℂ`. -/
theorem commutingEndomorphismDimension :
    CommutingEndomorphismDimensionStatement.{uV} := by
  intro V _ _ _ l a hc
  exact CommutingDimension.commuting_dimension_nat ℂ V l a hc

end Langlands
