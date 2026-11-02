import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteLaurentDomainReduction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RadicalRadiusStrictification
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictDomainComparison

/-! # Full finite rational coverage from strict local Gerritzen–Grauert -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

variable (hGG : StrictTestDomain.LocalRationalNeighborhoodStatement.{u})
  {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (U : Domain K A)

include hGG

/-- Simultaneous Laurent reduction, strict comparison, compactness and descent
give a finite ambient rational cover from the strict local theorem. -/
theorem nonempty_finiteRationalCover_of_strictLocal :
    Nonempty (FiniteRationalCover U) := by
  obtain ⟨D, hK, hA, hU⟩ :=
    LaurentReduction.exists_strictifiable (K := K) (A := A) (U := U)
  obtain ⟨P, ⟨eA⟩⟩ := RadicalStrictification.exists_strictPresentation
    D.extension.L D.ambient hA
  obtain ⟨Q, ⟨eU⟩⟩ := RadicalStrictification.exists_strictPresentation
    D.extension.L D.domain.algebra hU
  let c : FiniteRationalCover D.domain :=
    FiniteRationalCover.ofNeighborhoods D.domain
      (fun x => nonempty_rationalNeighborhood_of_strict eA eU hGG hK x)
  exact ⟨D.descendCover c⟩

/-- Choose the actual ambient charts and bounded restrictions furnished by the
conditional construction. -/
def finiteRationalCoverOfStrictLocal : FiniteRationalCover U :=
  Classical.choice (nonempty_finiteRationalCover_of_strictLocal hGG U)

/-- The only analytic hypothesis of this assembly is strict local
Gerritzen–Grauert; the original field and both presentations are unrestricted. -/
theorem finiteRationalCoverStatement_of_strictLocal :
    FiniteRationalCoverStatement.{u} := by
  intro K _ _ _ A U
  let c := finiteRationalCoverOfStrictLocal hGG U
  exact ⟨c.size, c.chart, c.map, c.covers⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
