import Langlands.Sheaf.Renard.InductionSheaf
import Mathlib.CategoryTheory.Equivalence

/-!
# Renard III.3.2: the actual homogeneous sheaf equivalence

Both functors are the actual induction sheaf and original-stalk restriction.
The equivalence, including its natural unit and counit, is a conclusion.
-/

namespace Langlands.Sheaf.Renard.HomogeneousEquivalence

open CategoryTheory
open Langlands.Induction
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.HomogeneousSections

attribute [local instance] homogeneousAction

/-- Renard's induction and original-stalk restriction are the two functors of an
actual category equivalence, under the original t.d. and countability hypotheses. -/
def Statement : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] (hG : Langlands.Topology.IsLocallyProfinite G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    ∃ e : Langlands.SmoothRep.{0, 0, 0} ℂ H ≌ SmoothActionSheaf G (LeftQuotient H),
      e.functor = InductionSheaf.functor hG H hH ∧
      e.inverse = pointRestriction H hG hH

/-- The induction sheaf has the original coefficient representation as its natural
identity-coset stalk, using the actual published point-restriction functor. -/
def OriginStalkStatement : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] (hG : Langlands.Topology.IsLocallyProfinite G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    Nonempty (InductionSheaf.functor hG H hH ⋙ pointRestriction H hG hH ≅
      𝟭 (Langlands.SmoothRep.{0, 0, 0} ℂ H))

end Langlands.Sheaf.Renard.HomogeneousEquivalence
