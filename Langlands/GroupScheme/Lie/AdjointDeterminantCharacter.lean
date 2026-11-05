import Langlands.GroupScheme.Lie.ActionDeterminant
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates

/-! # The rational determinant character of the full adjoint action -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The actual rational character det(Ad) of an affine finite-type field group. -/
def adjointDeterminantCharacter : rationalCharacters G :=
  (AutomorphicAction.conjugation (𝟙 G)).determinantCharacter (finiteCoordinates G)

/-- On every affine test this character is the determinant of actual conjugation
on the dual-number identity kernel. -/
theorem adjointDeterminantCharacter_affinePoints
    (A : CommAlgCat.{u} (CommRingCat.of k)) (g : G.affinePoints A) :
    Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
        (g ≫ (adjointDeterminantCharacter G).toMul.hom.hom) =
      LinearEquiv.det ((AutomorphicAction.conjugation (𝟙 G)).differential g) :=
  (AutomorphicAction.conjugation (𝟙 G)).determinantCharacter_affinePoints
    (finiteCoordinates G) A g

/-- The intrinsic adjoint endomorphism has the same determinant; no coordinate
representation occurs on the right. -/
theorem adjointDeterminantCharacter_val
    (A : CommAlgCat.{u} (CommRingCat.of k)) (g : G.affinePoints A) :
    (Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
        (g ≫ (adjointDeterminantCharacter G).toMul.hom.hom)).val =
      LinearMap.det (adjoint G A g) := by
  rw [adjointDeterminantCharacter_affinePoints, LinearEquiv.coe_det]
  congr 1
  apply LinearMap.ext
  intro x
  simpa using AutomorphicAction.differential_conjugation (𝟙 G) g x

end Langlands.GroupScheme.Lie
