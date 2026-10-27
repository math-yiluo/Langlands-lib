import Langlands.ClassFieldTheory.Local.ClassFormation
import Langlands.ClassFieldTheory.Local.TateInflation
import Langlands.ClassFieldTheory.Local.TateTransferCompatibility
import Langlands.ClassFieldTheory.Local.OrdinaryCupInflation
import Langlands.Cohomology.Tate.TateTheoremStatement

/-!
# Cup-product consequences of the finite class-formation axioms

For an arbitrary raw invariant family satisfying the finite relative
class-formation predicate, the fundamental-class cup laws follow: the Tate
isomorphisms (given Tate's theorem), the scaled inflation diagrams, and the
restriction and corestriction diagrams. These are conditional statements; they
realize no invariant family.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Tate's theorem turns the finite class-formation axioms into bijectivity of
left cup with every fundamental class, in every integer Tate degree. -/
def ClassFormationTateIsomorphismsStatement : Prop :=
  Langlands.Tate.TateCupIsomorphism.{u} →
    ∀ (p : ℕ) [Fact p.Prime] (I : InvariantFamily.{u,u} p),
      I.RelativeClassFormation → I.TateIsomorphisms

/-- The finite class-formation axioms give the degree-scaled fundamental-class
cup inflation diagrams, in positive Tate degrees and in every ordinary degree. -/
def ClassFormationInflationLawsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : InvariantFamily.{u,u} p),
    I.RelativeClassFormation → I.PositiveTateInflation ∧ I.OrdinaryInflation

/-- The finite class-formation axioms give the unscaled fundamental-class cup
restriction and corestriction diagrams in every integer Tate degree. -/
def ClassFormationTransferLawsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : InvariantFamily.{u,u} p),
    I.RelativeClassFormation → I.TateTransferCompatibility

end Langlands.ClassFieldTheory.Local
