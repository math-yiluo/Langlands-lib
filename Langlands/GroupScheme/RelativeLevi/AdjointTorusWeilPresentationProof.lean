import Langlands.GroupScheme.RelativeLevi.AdjointTorusWeilPresentationStatement
import Langlands.GroupScheme.Reductive.SuppliedBorelPermutationAtlas
import Langlands.GroupScheme.Torus.EtalePermutationWeilPresentation

/-! # The adjoint torus of a relative Borel is a finite etale Weil torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A supplied maximal torus in a relative Borel has the asserted actual
finite projective etale Weil presentation for any full central fppf quotient. -/
theorem relativeBorelAdjointTorusWeilPresentation :
    RelativeBorelAdjointTorusWeilPresentationStatement.{u} := by
  intro R _ G B i hG hi T t hT ht hmax D q hq
  exact permutationAtlasWeilPresentation R D
    ((SuppliedBorelAtlas.ofData hG hi hT ht hmax).hasEtalePermutationAtlas q hq)

end Langlands.GroupScheme
