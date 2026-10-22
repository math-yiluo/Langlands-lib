import Langlands.Cohomology.Continuous.InnerConjugation

/-! # Inner conjugation is trivial on continuous degree-two cohomology -/

open CategoryTheory

namespace Langlands.Continuous

universe u v w

/-- The actual inner-conjugation map is the identity on degree-two continuous
cohomology of a compact Hausdorff group, with arbitrary topological coefficients. -/
def InnerConjugationH2Triviality : Prop :=
  ∀ (k : Type u) (G : Type v) [Ring k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] (A : TopRep.{max v w} k G) (a : G),
    innerConjugationMap A a 2 = 𝟙 (continuousCohomology 2 A)

end Langlands.Continuous
