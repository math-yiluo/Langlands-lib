import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.GeneralLinearPointTopology
import Langlands.GroupScheme.GeneralLinearCoordinateSmooth
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps

/-! # Regular functions through a closed matrix representation

For a closed matrix representation `ρ` of an affine group scheme over a field, every global
regular function is a polynomial in the matrix entries and inverse-matrix entries of `ρ`, uniformly
in all points.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Every global regular function is a polynomial in the entries and inverse entries of a closed
representation, evaluated at every affine point. -/
theorem exists_polynomial_affinePointEvaluation (ρ : MatrixRepresentation G n)
    (hρ : IsClosedSubgroup ρ) (b : Γ(G.X.left, ⊤)) :
    ∃ P : MvPolynomial (Coordinate n) k, ∀ (S : CommAlgCat.{u} (CommRingCat.of k))
      (x : G.affinePoints S),
      G.affinePointEvaluation S x b = MvPolynomial.aeval (values (ρ.affineMatrix S x)) P := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsAffine (Grp.toMon (GeneralLinear.groupScheme n (CommRingCat.of k))).X.left :=
    GeneralLinear.isAffine_groupScheme n (CommRingCat.of k)
  let π : MvPolynomial (Coordinate n) k →ₐ[k] AffineCoordinateRing k G.X :=
    (affineCoordinatePullback k ρ.hom.hom).comp
      ((spectrumCoordinateAlgEquiv k (CoordinateRing n k)).symm.toAlgHom.comp (quotient n k))
  have hπ : Function.Surjective π :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ρ.hom.hom.left).2.comp
      ((spectrumCoordinateAlgEquiv k (CoordinateRing n k)).symm.surjective.comp
        Ideal.Quotient.mk_surjective)
  obtain ⟨P, hP⟩ := hπ b
  refine ⟨P, fun S x => ?_⟩
  rw [← hP]
  let c : Γ((GeneralLinear.groupScheme n (CommRingCat.of k)).X.left, ⊤) :=
    (spectrumCoordinateAlgEquiv k (CoordinateRing n k)).symm (quotient n k P)
  change G.affinePointEvaluation S x (ρ.hom.hom.left.appTop c) = _
  rw [← affinePointEvaluation_postcomp]
  have hy : x ≫ ρ.hom.hom = (affinePointsEquiv n (CommRingCat.of k) S).symm
      (ρ.affineMatrix S x) := by
    rw [affineMatrix_apply, MulEquiv.symm_apply_apply]
  rw [hy, affinePointsEquiv_symm_apply, affinePointEvaluation_map_classify]
  have hc : (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n (CommRingCat.of k)))).hom c =
      quotient n k P := by
    exact (spectrumCoordinateAlgEquiv k (CoordinateRing n k)).apply_symm_apply _
  rw [hc, classify_quotient]

end Langlands.GroupScheme.MatrixRepresentation
