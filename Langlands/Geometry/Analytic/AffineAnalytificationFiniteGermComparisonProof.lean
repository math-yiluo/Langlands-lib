import Langlands.Geometry.Analytic.AffineAnalytificationFiniteGermAssembly
import Langlands.Geometry.Analytic.FinitePieceLocalProof
import Langlands.Geometry.Analytic.AffineAnalytificationChartFlatProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessProof

/-! # Proof: flatness and unramifiedness at a point where the analytification is finite -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open PresentedAffinoidAlgebra

/-- The finite-germ comparison, given flatness of the chart algebras of an affine
analytification and of the structural maps of affinoid domains. -/
theorem finiteGermComparison_of_flatness
    (hchart : AffineAnalytificationChartFlatStatement.{u, v})
    (hdom : Domain.FlatnessStatement.{u}) :
    AffineAnalytificationFiniteGermComparisonStatement.{u, v, w} :=
  finiteGermComparison_of_finitePieceLocal
    (FinitePieceLocal.affineAnalytificationFinitePieceLocal hchart hdom)

/-- At a point where the affine analytification map is finite, flatness and unramifiedness of
the analytic germ agree with flatness and unramifiedness of the algebraic local ring map. -/
theorem affineAnalytificationFiniteGermComparison :
    AffineAnalytificationFiniteGermComparisonStatement.{u, v, w} :=
  finiteGermComparison_of_flatness affineAnalytificationChartFlat Domain.flatness

end Langlands.Analytic.AffineAnalytification
