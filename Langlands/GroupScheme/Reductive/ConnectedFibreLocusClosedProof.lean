import Langlands.GroupScheme.Reductive.ConnectedFibreLocusReduction
import Langlands.GroupScheme.Reductive.ConnectedFibreLocusDvrCoreProof

/-! # Proof: the locus of connected fibres is closed -/

universe u

namespace Langlands.GroupScheme

/-- **The connected-fibre locus is closed** (Conrad, *Reductive group schemes* (2014),
Proposition 3.1.12): for a smooth `S`-affine group whose geometric fibres have reductive
identity components, the set of points with connected fibre is closed, and a connected
generic fibre forces all fibres to be connected. -/
theorem connectedFibreLocusClosed : ConnectedFibreLocusClosedStatement.{u} :=
  ConnectedFibreLocus.connectedFibreLocusClosed_of_dvrCore ConnectedFibreLocus.dvrCore

end Langlands.GroupScheme
