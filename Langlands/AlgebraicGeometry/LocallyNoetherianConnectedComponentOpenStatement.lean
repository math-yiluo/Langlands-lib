import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Connected.Basic

/-! # Openness of connected components of a locally Noetherian scheme -/

universe u

namespace Langlands.AlgebraicGeometry

/-- In every locally Noetherian scheme, the connected component of each point of
the underlying topological space is open. -/
def LocallyNoetherianConnectedComponentOpenStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
    (x : X), IsOpen (connectedComponent x)

end Langlands.AlgebraicGeometry
