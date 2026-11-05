import Langlands.GroupScheme.AffinePointCoordinateJet
import Langlands.GroupScheme.MatrixRepresentationProductDifferentialConjugation
import Langlands.GroupScheme.GeneralLinearPointTopology

/-! # Output coefficients of actual representation first jets -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinear GeneralLinearProductDualNumber

set_option backward.isDefEq.respectTransparency false

variable {J : Type u} [Fintype J]
  {n : J → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  {R : CommRingCat.{u}}
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [Algebra R B]
  {m : Type} [Fintype m] [DecidableEq m]

/-- An actual coordinate jet is carried by the representation to the derivative
specified by its independent dual-number differential, entry by entry. -/
theorem hasDerivAt_productMatrixPointsHom_of_coordinateJet
    (ρ : MatrixRepresentation (groupScheme n R) m)
    (g : ℝ → ∀ j, GL (n j) B) (X : ∀ j, Matrix (n j) (n j) B) (t : ℝ)
    (h : (groupScheme n R).CoordinateJet
      (fun s => (affineMatrixEquiv (n := n) (R := R) B).symm (g s))
      (pointUnit X) t)
    (i j : m) :
    HasDerivAt (fun s => ρ.productMatrixPointsHom B (g s) i j)
      (ρ.productDifferential B X i j) t := by
  have hi := ((h.postcomp ρ.hom.hom) (entrySection m R i j)).2
  convert hi using 1
  · funext s
    exact affinePointsEquiv_entry_evaluation m R (CommAlgCat.of R B)
      ((affineMatrixEquiv B).symm (g s) ≫ ρ.hom.hom) i j
  · rw [ρ.productDifferential_coefficients X]
    change (ρ.affineMatrix (CommAlgCat.of R (DualNumber B)) (pointUnit X) i j).snd = _
    exact congrArg TrivSqZeroExt.snd
      (affinePointsEquiv_entry_evaluation m R (CommAlgCat.of R (DualNumber B))
        (pointUnit X ≫ ρ.hom.hom) i j)

end Langlands.GroupScheme.MatrixRepresentation
