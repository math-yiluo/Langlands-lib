import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceMatching

/-! # Generation of matching families from generation of the pieces -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

/-- For finite local algebras with pair transitions, a full domain `V` and any
finite full-domain cover `e` of `V`: if, over every member of `e`, the
components of the restrictions of finitely many matching families over `V`
generate every piece, then these matching families generate the matching
families over `V` as a module over `V.algebra`. -/
def PieceMatchingLocalGenerationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (R : PresentedAffinoidAlgebra K) (c : Domain.FiniteCover (Domain.whole K R))
    (F : LocalAlgebras c) (t : PairTransitions F) (V : Domain K R)
    (e : Domain.FiniteCover V) (n : ℕ) (s : Fin n → t.pieceMatching V),
    (∀ a, t.PiecesGenerate (e.obj a)
      (fun k => t.matchingRestrict (Domain.Inclusion.subset (e.map a)) (s k))) →
    t.Generates V s

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
