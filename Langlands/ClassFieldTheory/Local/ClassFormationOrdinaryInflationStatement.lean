import Langlands.ClassFieldTheory.Local.ClassFormation
import Langlands.ClassFieldTheory.Local.TateTransferCompatibility
import Langlands.ClassFieldTheory.Local.OrdinaryCupInflation

/-!
# Simultaneous local realization with ordinary cup inflation

One raw invariant family satisfies the invariant, fundamental-class and Tate
transfer clauses, together with ordinary cup inflation in every natural degree.
Fundamental-class existence belongs to this same existential witness.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Local realization on one invariant family, including the degree-scaled
ordinary cup inflation diagram in every natural degree, including zero. -/
def LocalOrdinaryInflationCompatibleClassFormationStatement : Prop :=
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
    I.PositiveTateInflation ∧
    I.TateTransferCompatibility ∧
    I.OrdinaryInflation

end Langlands.ClassFieldTheory.Local
