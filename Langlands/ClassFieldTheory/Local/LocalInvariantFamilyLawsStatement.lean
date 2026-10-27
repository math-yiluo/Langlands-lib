import Langlands.ClassFieldTheory.Local.LocalInvariantFamily
import Langlands.ClassFieldTheory.Local.ClassFormation

/-!
# Laws of the local invariant family

Five propositions about the family `localInvariantFamily hEx p` built from an
unramified `H²` exhaustion proof `hEx`. They state that this one family has the
continuous absolute invariant properties, the three invariant clauses of the
finite relative class-formation predicate, and arithmetic normalization. The
module defines propositions only.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The local invariant family satisfies Hilbert 90 for the algebraic closure,
has bijective absolute invariants that multiply by the degree under absolute
restriction, and is compatible with closure inflation on every ordinary
relative class. -/
def LocalInvariantFamilyContinuousStatement : Prop :=
  ∀ (hEx : UnramifiedH2Exhaustion.{u}) (p : ℕ) [Fact p.Prime],
    (localInvariantFamily hEx p).ContinuousInvariantProperties

/-- The relative invariants of the local invariant family are injective, with
image the subgroup of `ℚ/ℤ` killed by the extension degree. -/
def LocalInvariantFamilyRelativeImagesStatement : Prop :=
  ∀ (hEx : UnramifiedH2Exhaustion.{u}) (p : ℕ) [Fact p.Prime],
    (localInvariantFamily hEx p).RelativeImages

/-- The relative invariants of the local invariant family agree along actual
inflation. -/
def LocalInvariantFamilyInflationStatement : Prop :=
  ∀ (hEx : UnramifiedH2Exhaustion.{u}) (p : ℕ) [Fact p.Prime],
    (localInvariantFamily hEx p).InflationCompatibility

/-- Actual relative restriction multiplies the relative invariants of the local
invariant family by the base-extension degree. -/
def LocalInvariantFamilyRestrictionStatement : Prop :=
  ∀ (hEx : UnramifiedH2Exhaustion.{u}) (p : ℕ) [Fact p.Prime],
    (localInvariantFamily hEx p).RelativeRestriction

/-- The local invariant family gives `1/n` on the cyclic class of a uniformizer
for every arithmetic unramified coordinate. -/
def LocalInvariantFamilyArithmeticStatement : Prop :=
  ∀ (hEx : UnramifiedH2Exhaustion.{u}) (p : ℕ) [Fact p.Prime],
    (localInvariantFamily hEx p).ArithmeticNormalization

end Langlands.ClassFieldTheory.Local
