import Langlands.Representation.Aubert.GeneralCorollaryTargets
import Langlands.Representation.Filtration.RepresentationLength

/-! # Algebraic target for extracting two actual constituents -/

namespace Langlands.Aubert.General

universe uG uV

/-- A nonzero reducible actual smooth representation of composition length at
most two has two actual finite-length irreducible constituents in a short
exact sequence. The composition-length bound is a hypothesis. -/
def TwoConstituentExtractionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G) [Nontrivial A],
    repLength A.representation ≤ 2 → ¬ A.IsIrreducible →
      ∃ ρplus ρminus : SmoothRep.FiniteLengthObject.{0, uG, uV} ℂ G,
        HasTwoConstituents A ρplus.val ρminus.val

end Langlands.Aubert.General
