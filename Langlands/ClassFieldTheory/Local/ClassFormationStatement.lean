import Langlands.ClassFieldTheory.Local.ClassFormation
import Langlands.ClassFieldTheory.Local.TateCup
import Langlands.ClassFieldTheory.Local.TateInflation

/-!
# Local realization targets for relative and continuous invariant properties

The invariant family and fundamental classes occur only in conclusions.
The combined target includes the actual finite-stage/absolute compatibility
diagram, finite corestriction, all-integer fundamental-class cup bijectivity,
and the degree-scaled positive Tate inflation law.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Local finite-level class formation and its fundamental classes, for every
prime and all p-adic fields in an arbitrary carrier universe. -/
def LocalRelativeClassFormationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ I : InvariantFamily.{u,u} p,
    I.ArithmeticNormalization ∧
    I.RelativeClassFormation ∧
    I.RelativeConjugacy ∧
    I.RelativeCorestriction ∧
    I.FundamentalClasses ∧
    I.FundamentalInflation ∧
    I.FundamentalRestriction ∧
    I.FundamentalCorestriction ∧
    I.FundamentalConjugacy

/-- One invariant family simultaneously realizes the continuous absolute
properties, finite relative class-formation properties, all-integer Tate
cup bijectivity, and positive Tate inflation compatibility.
The finite-stage diagram uses the proved comparison. -/
def LocalCompatibleClassFormationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ I : InvariantFamily.{u,u} p,
    I.ArithmeticNormalization ∧
    I.ContinuousInvariantProperties ∧
    I.RelativeClassFormation ∧
    I.RelativeConjugacy ∧
    I.RelativeCorestriction ∧
    I.FundamentalClasses ∧
    I.FundamentalInflation ∧
    I.FundamentalRestriction ∧
    I.FundamentalCorestriction ∧
    I.FundamentalConjugacy ∧
    I.TateIsomorphisms ∧
    I.PositiveTateInflation

/-- Conditional finite-level consequences of the honest class-formation axiom
schema. This generic implication accompanies, and does not replace, local
realization in `LocalRelativeClassFormationStatement`. -/
def RelativeFundamentalClassConsequencesStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : InvariantFamily.{u,u} p),
    I.RelativeClassFormation → I.RelativeConjugacy →
      I.FundamentalClasses ∧ I.FundamentalInflation ∧
        I.FundamentalRestriction ∧ I.FundamentalCorestriction ∧
        I.FundamentalConjugacy

end Langlands.ClassFieldTheory.Local
