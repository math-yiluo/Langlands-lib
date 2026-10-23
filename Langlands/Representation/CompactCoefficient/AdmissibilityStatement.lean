import Langlands.Representation.CompactCoefficient.Classes

/-! Admissibility of irreducible smooth representations with compact coefficients. -/

namespace Langlands

universe uG uV

/-- BZ76 Corollary 2.41, restricted to irreducibles. Admissibility is a
conclusion about all actual open-subgroup fixed spaces. -/
def CompactCoefficientIrreducibleAdmissibilityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G),
    A.IsIrreducible →
    HasCompactSmoothDualCoefficients A.representation →
    A.IsAdmissible

end Langlands
