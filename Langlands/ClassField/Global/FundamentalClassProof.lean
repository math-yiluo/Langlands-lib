import Langlands.ClassField.Global.FundamentalClassReduction
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.ClassField.Global.InvariantProof

/-! # Global class field theory in fundamental-class form -/

namespace Langlands.ClassField.Global

universe u

open Langlands.ClassFieldTheory.Local FundamentalClass

/-- **Existence** of a coherent family of global fundamental classes for a local family `I`
satisfying the class-formation axioms and the arithmetic normalization. -/
theorem fundamentalClass_exists
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) :
    ∃ c : ClassFamily.{u},
      Generates c ∧ Restriction c ∧ Inflation c ∧ LocalCompatibility I c :=
  fundamentalClass_exists_of globalInvariantStatement.{u} I hI

/-- **Uniqueness** of the family of global fundamental classes: two families that satisfy
`Inflation` and `LocalCompatibility I` are equal. -/
theorem fundamentalClass_unique
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    {c c' : ClassFamily.{u}} (hc : Inflation c ∧ LocalCompatibility I c)
    (hc' : Inflation c' ∧ LocalCompatibility I c') : c = c' :=
  fundamentalClass_unique_of globalInvariantStatement.{u} I hI hc hc'

/-- **Global class field theory in fundamental-class form**: `H¹(Gal(E/F), C_E) = 0`, and
there is a unique coherent family of global fundamental classes. -/
theorem globalFundamentalClassStatement : GlobalFundamentalClassStatement.{u} :=
  globalFundamentalClassStatement_of ideleClassH1Vanishing.{u} globalInvariantStatement.{u}

end Langlands.ClassField.Global
