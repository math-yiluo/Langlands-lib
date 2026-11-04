import Langlands.GroupScheme.Lie.SemisimpleJordanCentralizer
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSpanningStatement

/-! # Descent and spanning by noncentral semisimple tangent centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000 in
/-- The exact universe-general noncentral semisimple centralizer spanning target. -/
theorem semisimpleCentralizerSpanning : SemisimpleCentralizerSpanningStatement.{u} := by
  intro k _ _ G _ _ _ hgeo
  exact semisimpleCentralizer_spanning_of_geometric_semisimple (K := AlgebraicClosure k) (finiteCoordinates G) hgeo

end Langlands.GroupScheme.Lie
