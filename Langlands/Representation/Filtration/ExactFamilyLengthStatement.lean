import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.Filtration.LengthCriterionStatement
import Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
import Langlands.Representation.Category.Subquotients

/-! A finite family of exact functors bounds length when it jointly detects
irreducible subquotients. -/

open CategoryTheory

namespace Langlands

/-- Internal length criterion for a finite family of exact smooth functors.
The target groups may vary with the family index. No finite-length assumption
on the source representation is made. -/
def ExactFamilyLengthBoundStatement.{uI, uG, uH, uV} : Prop :=
  ∀ (ι : Type uI) [Fintype ι]
    (G : Type uG) [Group G] [TopologicalSpace G]
    (H : ι → Type uH) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    (F : ∀ i, SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ (H i)),
    (∀ i, Derivative.Mirabolic.MapsShortExactIntertwiners (F i)) →
    ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (b : ι → ℕ),
      (∀ i, repLength ((F i).obj A).representation ≤ (b i : ℕ∞)) →
      (∀ D : SmoothRep.{0, uG, uV} ℂ G,
        D.IsIrreducible → SmoothRep.IsSubquotient D A →
        ∃ i, Nontrivial ((F i).obj D)) →
      HasCompositionLengthAtMost A.obj (∑ i, b i)

end Langlands
