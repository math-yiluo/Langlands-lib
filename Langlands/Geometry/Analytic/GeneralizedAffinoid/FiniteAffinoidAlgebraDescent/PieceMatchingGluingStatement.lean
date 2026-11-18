import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceMatching

/-! # Gluing of matching families of pieces along finite covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

/-- For finite local algebras with pair transitions, a full domain `V` and any
finite full-domain cover `e` of `V`: matching families over the members of `e`
whose restrictions agree on every literal pairwise intersection come from a
unique matching family over `V`. -/
def PieceMatchingGluingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (R : PresentedAffinoidAlgebra K) (c : Domain.FiniteCover (Domain.whole K R))
    (F : LocalAlgebras c) (t : PairTransitions F) (V : Domain K R)
    (e : Domain.FiniteCover V) (m : ∀ a, t.pieceMatching (e.obj a)),
    (∀ a b, t.matchingRestrict (V' := (e.obj a).inter (e.obj b)) Set.inter_subset_left (m a) =
      t.matchingRestrict (V' := (e.obj a).inter (e.obj b)) Set.inter_subset_right (m b)) →
    ∃! x : t.pieceMatching V,
      ∀ a, t.matchingRestrict (Domain.Inclusion.subset (e.map a)) x = m a

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
