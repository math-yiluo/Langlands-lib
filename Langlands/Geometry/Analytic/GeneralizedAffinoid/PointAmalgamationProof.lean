import Langlands.Geometry.Analytic.ValuedField.AmalgamationProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.PointAmalgamationReduction

/-! # Common complete-field realization of compatible affinoid points -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- Compatible affinoid points are realized by commuting bounded algebra maps
into one complete ultrametric field in the same universe. -/
theorem pointAmalgamation : PointAmalgamationStatement.{u} :=
  pointAmalgamation_of_completeFieldAmalgamation completeFieldAmalgamation

end Langlands.Analytic.PresentedAffinoidAlgebra
