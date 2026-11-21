import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.GroupScheme.Rational.RealAnisotropicCompactConnectedProof
import Langlands.GroupScheme.Rational.RealAnisotropicFormCompactReduction
import Langlands.GroupScheme.Rational.RealCompactFormExistenceProof
import Langlands.GroupScheme.Rational.RealCompactFormUniquenessProof

/-! # The anisotropic form of a real semisimple group -/

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Every real semisimple group scheme has an anisotropic semisimple form,
unique up to isomorphism over ℝ (Milne, Theorem 25.56). -/
theorem realAnisotropicForm : RealAnisotropicFormStatement := by
  refine realAnisotropicForm_of_compactFormInputs
    ⟨realCompactFormExistence, realCompactFormUniqueness, ?_⟩
  intro G hG hA
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : CompactSpace (RingPoint ℝ G.X ℝ) := (realAnisotropicCompactConnected G hG hA).1
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of ℝ ℝ)
  let : CompactSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    (G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ)).symm.compactSpace
  exact isCompact_univ

end Langlands.GroupScheme
