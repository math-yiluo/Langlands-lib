import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticStructure

/-! # Uniqueness of admissible varying-dimension analytic structures -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Any two admissible varying-dimension analytic structures are equivalent:
on the original rational points of every smooth, quasi-separated, locally
separated space, the identity is analytic in both directions. -/
def SmoothSourceDimensionAnalyticUniquenessStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (Φ Ψ : DimensionAnalyticStructure K),
    Φ.IsAdmissible → Ψ.IsAdmissible → Φ.Equivalent Ψ

end Langlands.AlgebraicGeometry.AlgebraicSpace
