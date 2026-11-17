import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.EffectiveData

/-! # Effective finite Banach algebra descent on arbitrary finite full-domain covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- Unrestricted effective finite Banach affinoid algebra descent. The matching
algebra, bounded structural map and canonical comparisons are constructed;
affinoid realization, norm-controlled finiteness and effectiveness are outputs. -/
def FiniteAffinoidAlgebraDescentStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (R : PresentedAffinoidAlgebra K)
    (c : Domain.FiniteCover (Domain.whole K R))
    (F : FiniteAffinoidAlgebraDescent.LocalAlgebras c)
    (d : FiniteAffinoidAlgebraDescent.DescentData F),
    Nonempty (FiniteAffinoidAlgebraDescent.EffectiveRealization d)

end Langlands.Analytic.PresentedAffinoidAlgebra
