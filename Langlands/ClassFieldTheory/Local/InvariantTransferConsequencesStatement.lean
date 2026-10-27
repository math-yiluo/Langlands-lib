import Langlands.ClassFieldTheory.Local.ClassFormation
import Langlands.ClassFieldTheory.Local.AbsoluteCorestrictionInvariant

/-!
# Conjugacy and corestriction laws from inflation and restriction laws

Three conditional propositions about an arbitrary raw invariant family. The
conjugacy law follows from the inflation and restriction laws, and the finite
and absolute corestriction laws follow from the image or bijectivity clauses
together with the corresponding restriction laws. The module defines
propositions only.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Inflation compatibility and the relative restriction law imply that
relative invariants commute with genuine conjugacy of p-adic extensions. -/
def InvariantRelativeConjugacyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : InvariantFamily.{u,u} p),
    I.InflationCompatibility → I.RelativeRestriction → I.RelativeConjugacy

/-- The relative image clause and the relative restriction law imply that
finite relative corestriction preserves relative invariants. -/
def InvariantRelativeCorestrictionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : InvariantFamily.{u,u} p),
    I.RelativeImages → I.RelativeRestriction → I.RelativeCorestriction

/-- Bijective absolute invariants with the absolute restriction law are
preserved by genuine absolute corestriction. -/
def InvariantAbsoluteCorestrictionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : InvariantFamily.{u,u} p),
    I.AbsoluteIsomorphisms → I.AbsoluteRestriction → I.AbsoluteCorestriction

end Langlands.ClassFieldTheory.Local
