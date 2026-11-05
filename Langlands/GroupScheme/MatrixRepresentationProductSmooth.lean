import Langlands.GroupScheme.ProductCoordinateSmooth
import Langlands.GroupScheme.GeneralLinearCoordinateSmooth
import Langlands.GroupScheme.MatrixRepresentationProductDifferentialConjugation

/-! # Smooth evaluation of actual finite-product matrix representations -/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry
open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {J : Type u} [Finite J]
  {n : J → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  {R : CommRingCat.{u}}
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [Algebra R B]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

local instance factorAffine (j : J) :
    IsAffine (GeneralLinear.groupScheme (n j) R).X.left :=
  GeneralLinear.isAffine_groupScheme (n j) R

local instance factorMatrixComplete (j : J) : CompleteSpace (Matrix (n j) (n j) B) :=
  inferInstanceAs (CompleteSpace (n j → n j → B))

namespace GeneralLinearProductDualNumber

/-- Smooth invertible matrix families define a coordinate-smooth family of
actual points of the categorical product scheme. -/
theorem coordinateSmooth_affineMatrixEquiv_symm
    (g : M → ∀ j, GL (n j) B)
    (hg : ∀ j, ContMDiff I 𝓘(ℝ, Matrix (n j) (n j) B) ∞ (fun x => g x j)) :
    (groupScheme n R).CoordinateSmooth (CommAlgCat.of R B) (RingHom.id B) I
      (fun x => (affineMatrixEquiv (n := n) (R := R) B).symm (g x)) := by
  apply coordinateSmooth_piPointsEquiv_symm
    (fun j => GeneralLinear.groupScheme (n j) R) (CommAlgCat.of R B) (RingHom.id B) I
  intro j
  apply (GeneralLinear.coordinateSmooth_iff_contMDiff (n j) R (CommAlgCat.of R B)
    (RingHom.id B) I _).mpr
  simp only [GeneralLinear.coefficientCoordinates, MonoidHom.comp_apply,
    Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
  change ContMDiff I 𝓘(ℝ, Matrix (n j) (n j) B) ∞
    (fun x => GeneralLinear.affinePointsEquiv (n j) R (CommAlgCat.of R B)
      ((GeneralLinear.affinePointsEquiv (n j) R (CommAlgCat.of R B)).symm (g x j)))
  simpa only [MulEquiv.apply_symm_apply] using hg j

end GeneralLinearProductDualNumber

namespace MatrixRepresentation

open GeneralLinearProductDualNumber

variable {m : Type} [Fintype m] [DecidableEq m]

local instance outputMatrixComplete : CompleteSpace (Matrix m m B) :=
  inferInstanceAs (CompleteSpace (m → m → B))

/-- Regularity is derived by postcomposing the actual product points with the
genuine scheme representation, then applying the GL regular-function criterion. -/
theorem contMDiff_productMatrixPointsHom
    (ρ : MatrixRepresentation (groupScheme n R) m)
    (g : M → ∀ j, GL (n j) B)
    (hg : ∀ j, ContMDiff I 𝓘(ℝ, Matrix (n j) (n j) B) ∞ (fun x => g x j)) :
    ContMDiff I 𝓘(ℝ, Matrix m m B) ∞ (fun x => ρ.productMatrixPointsHom B (g x)) := by
  have hp := coordinateSmooth_affineMatrixEquiv_symm (R := R) (n := n) I g hg
  have h := (GeneralLinear.coordinateSmooth_iff_contMDiff m R (CommAlgCat.of R B)
    (RingHom.id B) I _).mp (hp.postcomp ρ.hom.hom)
  simp only [GeneralLinear.coefficientCoordinates, MonoidHom.comp_apply,
    Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom] at h
  change ContMDiff I 𝓘(ℝ, Matrix m m B) ∞
    (fun x => GeneralLinear.affinePointsEquiv m R (CommAlgCat.of R B)
      ((affineMatrixEquiv (n := n) (R := R) B).symm (g x) ≫ ρ.hom.hom))
  exact h

end MatrixRepresentation

end Langlands.GroupScheme
