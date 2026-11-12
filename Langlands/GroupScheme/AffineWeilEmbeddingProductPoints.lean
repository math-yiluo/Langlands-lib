import Langlands.GroupScheme.AffineWeilEmbeddingCoordinates
import Langlands.GroupScheme.AffineWeilUnit
import Langlands.GroupScheme.AffinePointPiProducts
import Langlands.GroupScheme.Products

/-! # Actual group points in embedding-product coordinates -/

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

/-- The original coefficient ring with scalar action through the chosen embedding. -/
def embeddingCoefficientAlgebra (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (τ : K →ₐ[k] Ω) : CommAlgCat.{u} (CommRingCat.of K) :=
  letI : Algebra K R := ((algebraMap Ω R).comp τ.toRingHom).toAlgebra
  CommAlgCat.of (CommRingCat.of K) R

/-- Coefficient change with its conjugate scalar action retained. -/
def embeddingCoefficientMap {R R' : CommAlgCat.{u} (CommRingCat.of Ω)}
    (a : R ⟶ R') (τ : K →ₐ[k] Ω) :
    embeddingCoefficientAlgebra k K Ω R τ ⟶ embeddingCoefficientAlgebra k K Ω R' τ :=
  CommAlgCat.ofHom
    (X := embeddingCoefficientAlgebra k K Ω R τ)
    (Y := embeddingCoefficientAlgebra k K Ω R' τ)
    { a.hom.toRingHom with commutes' b := a.hom.commutes (τ b) }

local instance coefficientBaseAlgebra (R : CommAlgCat.{u} (CommRingCat.of Ω)) :
    Algebra k R := Algebra.compHom R (algebraMap k Ω)

local instance coefficientScalarTower (R : CommAlgCat.{u} (CommRingCat.of Ω)) :
    IsScalarTower k Ω R := IsScalarTower.of_algebraMap_eq' rfl

variable [Finite (K →ₐ[k] Ω)]
  (hsplit : Function.Bijective (embeddingEvaluation k K Ω))

/-- The canonical tensor decomposition, as an algebra equivalence with the original K-actions. -/
def tensorEmbeddingAlgEquiv (R : CommAlgCat.{u} (CommRingCat.of Ω)) :
    K ⊗[k] R ≃ₐ[K] (∀ τ, embeddingCoefficientAlgebra k K Ω R τ) where
  __ := tensorEmbeddingEquiv k K Ω hsplit R
  commutes' b := by
    funext τ
    change tensorEmbeddingEquiv k K Ω hsplit R (b ⊗ₜ[k] 1) τ = _
    simp only [tensorEmbeddingEquiv_tmul, mul_one]
    rfl

/-- Evaluation is an algebra map to precisely the corresponding conjugate coefficient algebra. -/
def tensorEmbeddingEvaluationMap (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (τ : K →ₐ[k] Ω) :
    CommAlgCat.of K (K ⊗[k] R) ⟶ embeddingCoefficientAlgebra k K Ω R τ :=
  CommAlgCat.ofHom (Y := embeddingCoefficientAlgebra k K Ω R τ)
    ((Pi.evalAlgHom K (fun τ => embeddingCoefficientAlgebra k K Ω R τ) τ).comp
      (tensorEmbeddingAlgEquiv k K Ω hsplit R).toAlgHom)

@[simp] theorem tensorEmbeddingEvaluationMap_ringHom
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω) :
    (tensorEmbeddingEvaluationMap k K Ω hsplit R τ).hom.toRingHom =
      tensorEmbeddingEvaluation k K Ω hsplit R τ := rfl

variable (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffine H.X.left]

/-- Tensor points of an arbitrary affine group form the product of its conjugate-coefficient points. -/
def tensorEmbeddingPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of Ω)) :
    H.affinePoints (CommAlgCat.of K (K ⊗[k] R)) ≃*
      (∀ τ, H.affinePoints (embeddingCoefficientAlgebra k K Ω R τ)) :=
  (H.affinePointFunctor.mapIso
    (CommAlgCat.isoMk (tensorEmbeddingAlgEquiv k K Ω hsplit R))).groupIsoToMulEquiv.trans
      (H.affinePointsPiEquiv (embeddingCoefficientAlgebra k K Ω R))

/-- Each coordinate is the actual point pullback along tensor evaluation. -/
theorem tensorEmbeddingPointsEquiv_apply (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : H.affinePoints (CommAlgCat.of K (K ⊗[k] R))) (τ : K →ₐ[k] Ω) :
    tensorEmbeddingPointsEquiv k K Ω hsplit H R p τ =
      H.affinePointMap (tensorEmbeddingEvaluationMap k K Ω hsplit R τ) p := by
  change H.affinePointMap _ (H.affinePointMap _ p) = _
  rw [← MonoidHom.comp_apply, ← affinePointMap_comp]
  rfl

/-- The original affine coordinates are followed by the published tensor evaluation. -/
theorem tensorEmbeddingPointsEquiv_coordinates
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : H.affinePoints (CommAlgCat.of K (K ⊗[k] R))) (τ : K →ₐ[k] Ω) :
    (affineSchemePointEquiv K H.X (embeddingCoefficientAlgebra k K Ω R τ)
      (tensorEmbeddingPointsEquiv k K Ω hsplit H R p τ)).toAlgHom.toRingHom =
      (tensorEmbeddingEvaluation k K Ω hsplit R τ).comp
        (affineSchemePointEquiv K H.X (K ⊗[k] R) p).toAlgHom.toRingHom := by
  rw [tensorEmbeddingPointsEquiv_apply]
  exact congrArg AlgHom.toRingHom
    (coordinatePoint_changeRing K H.X
      (tensorEmbeddingEvaluationMap k K Ω hsplit R τ).hom p)

/-- Evaluation commutes with every original coefficient map. -/
theorem tensorEmbeddingEvaluationMap_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of Ω)} (a : R ⟶ R') (τ : K →ₐ[k] Ω) :
    CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := K) K
        (a.hom.restrictScalars k)) ≫ tensorEmbeddingEvaluationMap k K Ω hsplit R' τ =
      tensorEmbeddingEvaluationMap k K Ω hsplit R τ ≫ embeddingCoefficientMap k K Ω a τ := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact tensorEmbeddingEvaluation_naturality k K Ω hsplit a.hom τ x

/-- The tensor group decomposition is natural in the coefficient algebra. -/
theorem tensorEmbeddingPointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of Ω)} (a : R ⟶ R')
    (p : H.affinePoints (CommAlgCat.of K (K ⊗[k] R))) (τ : K →ₐ[k] Ω) :
    tensorEmbeddingPointsEquiv k K Ω hsplit H R'
        (H.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor
          (S := K) K (a.hom.restrictScalars k))) p) τ =
      H.affinePointMap (embeddingCoefficientMap k K Ω a τ)
        (tensorEmbeddingPointsEquiv k K Ω hsplit H R p τ) := by
  rw [tensorEmbeddingPointsEquiv_apply, tensorEmbeddingPointsEquiv_apply,
    ← MonoidHom.comp_apply, ← affinePointMap_comp,
    tensorEmbeddingEvaluationMap_naturality, affinePointMap_comp]
  rfl

end Langlands.GroupScheme.AffineWeil
