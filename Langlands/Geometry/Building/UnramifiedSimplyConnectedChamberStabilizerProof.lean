import Langlands.Geometry.Building.UnramifiedSimplyConnectedChamberStabilizerReduction
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof

/-! # Simply connected chamber stabilizers over the maximal unramified extension -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.MaximalUnramified

/-- Chamber stabilizers of any supplied building datum for a simply connected
group over the actual maximal unramified field fix the chamber pointwise. -/
theorem simplyConnectedChamberStabilizer :
    SimplyConnectedChamberStabilizerStatement.{u} :=
  simplyConnectedChamberStabilizerReduction simplyConnectedNormalizerAffineWeyl

end Langlands.Geometry.Building.MaximalUnramified
