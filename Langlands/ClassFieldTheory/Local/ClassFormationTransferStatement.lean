import Langlands.ClassFieldTheory.Local.ClassFormation
import Langlands.ClassFieldTheory.Local.TateInflation
import Langlands.ClassFieldTheory.Local.TateTransferCompatibility

/-!
# Simultaneous local realization with Tate transfer compatibility

Every property belongs to the same existentially quantified raw invariant
family. Fundamental-class existence makes the cup conditions nonvacuous.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Local realization of continuous and relative invariant properties,
fundamental classes, all-integer Tate cup isomorphisms and transfer diagrams,
and the degree-scaled positive Tate inflation diagram, on one family. -/
def LocalTransferCompatibleClassFormationStatement : Prop :=
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
    I.TateTransferCompatibility

end Langlands.ClassFieldTheory.Local
