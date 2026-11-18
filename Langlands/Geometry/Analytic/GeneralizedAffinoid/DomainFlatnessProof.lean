import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessReduction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartFlatness

/-! # Algebraic flatness of full affinoid-domain restrictions -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

/-- The structural map of every full represented affinoid domain is flat as a
homomorphism of the underlying commutative rings. -/
theorem flatness : FlatnessStatement.{u} :=
  flatnessStatement_of_chartFlat fun _ _ _ _ _ d => RationalChart.flat_baseMap d

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
