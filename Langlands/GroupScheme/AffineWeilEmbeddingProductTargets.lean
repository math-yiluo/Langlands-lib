import Langlands.GroupScheme.AffineWeilEmbeddingProductComparison
import Langlands.GroupScheme.AffineWeilEmbeddingProductMaps

/-! # Target homomorphisms in the embedding-product point comparisons -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

open Langlands.Algebra.SeparableTensor
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K Ω : Type u) [CommRing k] [CommRing K] [CommRing Ω]
  [Algebra k K] [Algebra k Ω]

attribute [local instance] coefficientBaseAlgebra coefficientScalarTower

section Tensor

variable [Finite (K →ₐ[k] Ω)]
  (hsplit : Function.Bijective (embeddingEvaluation k K Ω))
  {H H' : GroupScheme (Spec (CommRingCat.of K))} [IsAffine H.X.left] [IsAffine H'.X.left]

/-- The tensor decomposition retains the original target homomorphism in every coordinate. -/
theorem tensorEmbeddingPointsEquiv_target (f : H ⟶ H')
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : H.affinePoints (CommAlgCat.of K (K ⊗[k] R))) (τ : K →ₐ[k] Ω) :
    tensorEmbeddingPointsEquiv k K Ω hsplit H' R (p ≫ f.hom.hom) τ =
      tensorEmbeddingPointsEquiv k K Ω hsplit H R p τ ≫ f.hom.hom := by
  rw [tensorEmbeddingPointsEquiv_apply, tensorEmbeddingPointsEquiv_apply,
    affinePointMap_apply, affinePointMap_apply, Category.assoc]

end Tensor

section Restriction

variable [Module.Finite k K] [Module.Projective k K]
  {H H' : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  [IsAffine H'.X.left] [LocallyOfFiniteType H'.X.hom]

/-- The inverse base-change comparison of the Weil restriction turns the base change of
`AffineWeil.map f` into `AffineWeil.map f`. -/
theorem affinePointsBaseChangeMulEquiv_symm_map (f : H ⟶ H')
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj
      (groupScheme k K H)).affinePoints R) :
    (affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H')).symm
        (p ≫ ((GroupScheme.baseChange (algebraBaseMap k Ω)).map (map k K f)).hom.hom) =
      (affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H)).symm p ≫
        (map k K f).hom.hom := by
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left]
  change (p.left ≫ ((Over.pullback (Spec.algebraMap k Ω)).map (map k K f).hom.hom).left) ≫
      pullback.fst (groupScheme k K H').X.hom (Spec.algebraMap k Ω) =
    ((affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H)).symm p).left ≫
      (map k K f).hom.hom.left
  rw [affinePointsBaseChangeMulEquiv_symm_left]
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]

/-- The original tensor-valued points of the base-changed Weil restriction turn the base change
of `AffineWeil.map f` into the original target homomorphism `f`. -/
theorem baseChangeTensorPointsEquiv_target (f : H ⟶ H')
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj
      (groupScheme k K H)).affinePoints R) :
    baseChangeTensorPointsEquiv k K Ω H' R
        (p ≫ ((GroupScheme.baseChange (algebraBaseMap k Ω)).map (map k K f)).hom.hom) =
      baseChangeTensorPointsEquiv k K Ω H R p ≫ f.hom.hom := by
  change pointsEquiv k K H' R
      ((affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H')).symm
        (p ≫ ((GroupScheme.baseChange (algebraBaseMap k Ω)).map (map k K f)).hom.hom)) =
    pointsEquiv k K H R ((affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H)).symm p) ≫
      f.hom.hom
  rw [affinePointsBaseChangeMulEquiv_symm_map]
  exact map_affinePoints k K f R _

end Restriction

end Langlands.GroupScheme.AffineWeil
