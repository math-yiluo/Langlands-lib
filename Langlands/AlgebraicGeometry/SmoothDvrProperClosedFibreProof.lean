import Langlands.AlgebraicGeometry.SmoothDvrProperClosedFibreStatement
import Langlands.AlgebraicGeometry.SmoothLocalProperClosedFibre

/-! # Properness of a smooth DVR family with proper closed fibre -/

universe u

namespace Langlands.AlgebraicGeometry

/-- Properness of the actual closed fibre implies properness over the DVR. -/
theorem smoothDvrProperClosedFibre : SmoothDvrProperClosedFibreStatement.{u} := by
  intro V _ _ _ X p hsm hsep hqc hconn hclosed
  let := hsm
  let := hsep
  let := hqc
  let := hconn
  exact isProper_of_smooth_of_proper_closedFibre p hclosed

end Langlands.AlgebraicGeometry
