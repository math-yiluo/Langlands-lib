import Langlands.ClassFieldTheory.Local.ClassFormationOrdinaryInflationStatement
import Langlands.ClassFieldTheory.Local.AbsoluteCorestrictionInvariant

/-!
# Simultaneous local realization with absolute corestriction

One raw invariant family satisfies all fourteen ordinary-inflation realization
clauses and the invariant law for genuine absolute corestriction. All laws and
fundamental-class existence are conclusions for this same witness.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Local realization on one invariant family, including unscaled absolute
corestriction for every finite compatible extension and supplied closure map. -/
def LocalAbsoluteCorestrictionCompatibleClassFormationStatement : Prop :=
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
    I.OrdinaryInflation ∧
    I.AbsoluteCorestriction

end Langlands.ClassFieldTheory.Local
