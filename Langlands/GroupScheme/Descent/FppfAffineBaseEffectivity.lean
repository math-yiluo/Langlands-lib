import Langlands.AlgebraicGeometry.AffineFppfRefinement
import Langlands.GroupScheme.Descent.AffineDatumGroup
import Langlands.GroupScheme.Descent.FppfReverseRefinement

/-! # fppf descent of affine groups over an affine base -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.Descent.Datum

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  (D : Datum p G) [IsAffine B] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  [IsAffineHom G.X.hom]

/-- Effective fppf descent over an affine base, with no affineness assumption on the cover. -/
def fppfAffineBaseSolution : Solution D := by
  have : Flat (Over.mk p).hom := ‹Flat p›
  have : Surjective (Over.mk p).hom := ‹Surjective p›
  have : LocallyOfFinitePresentation (Over.mk p).hom := ‹LocallyOfFinitePresentation p›
  let R := Langlands.AlgebraicGeometry.affineFppfRefinement (Over.mk p)
  have : IsAffine R.cover.left := R.isAffine
  have : Flat R.cover.hom := R.flat
  have : Surjective R.cover.hom := R.surjective
  have : LocallyOfFinitePresentation R.cover.hom := R.locallyOfFinitePresentation
  have hR : R.map.left ≫ p = R.cover.hom := Over.w R.map
  have : Flat (R.map.left ≫ p) := by rw [hR]; infer_instance
  have : Surjective (R.map.left ≫ p) := by rw [hR]; infer_instance
  have : LocallyOfFinitePresentation (R.map.left ≫ p) := by rw [hR]; infer_instance
  have : IsAffine ((Langlands.GroupScheme.baseChange R.map.left).obj G).X.left := by
    change IsAffine (pullback G.X.hom R.map.left)
    infer_instance
  exact D.fppfSolutionOfRefinement R.map.left (D.refine R.map.left).affineSolution

instance fppfAffineBaseSolution_isAffine :
    IsAffine D.fppfAffineBaseSolution.obj.X.left := by
  dsimp only [fppfAffineBaseSolution, fppfSolutionOfRefinement]
  infer_instance

end Langlands.GroupScheme.Descent.Datum
