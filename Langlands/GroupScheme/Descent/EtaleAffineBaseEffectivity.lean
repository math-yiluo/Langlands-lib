import Langlands.GroupScheme.Descent.AffineEtaleRefinement
import Langlands.GroupScheme.Descent.AffineDatumGroup
import Langlands.GroupScheme.Descent.ReverseRefinement

/-! # Étale descent of affine groups over an affine base -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.Descent.Datum

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  (D : Datum p G) [IsAffine B] [Etale p] [Surjective p] [IsAffineHom G.X.hom]

/-- Effective descent over an affine base, with no affineness assumption on the cover. -/
def etaleAffineBaseSolution : Solution D := by
  let R := affineEtaleRefinement p
  have : IsAffine ((Langlands.GroupScheme.baseChange R.map).obj G).X.left := by
    change IsAffine (pullback G.X.hom R.map)
    infer_instance
  exact D.solutionOfRefinement R.map (D.refine R.map).affineSolution

instance etaleAffineBaseSolution_isAffine :
    IsAffine D.etaleAffineBaseSolution.obj.X.left := by
  dsimp only [etaleAffineBaseSolution, solutionOfRefinement]
  infer_instance

end Langlands.GroupScheme.Descent.Datum
