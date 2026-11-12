import Langlands.GroupScheme.AffineWeilEmbeddingProductComparison
import Langlands.GroupScheme.AffinePointComparison

/-! # Actual evaluation of affine Weil restriction after scalar extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]

attribute [local instance] coefficientBaseAlgebra coefficientScalarTower

/-- Multiplication of the original scalar factor into a coefficient algebra. -/
def evaluationCoefficientMap (R : CommAlgCat.{u} (CommRingCat.of K)) :
    CommAlgCat.of K (K ⊗[k] R) ⟶ R :=
  CommAlgCat.ofHom ((AlgHom.liftEquiv k K R R) (AlgHom.id k R))

@[simp] theorem evaluationCoefficientMap_tmul
    (R : CommAlgCat.{u} (CommRingCat.of K)) (b : K) (r : R) :
    (evaluationCoefficientMap k K R).hom (b ⊗ₜ[k] r) =
      algebraMap K R b * r := by
  simp [evaluationCoefficientMap, Algebra.smul_def]

/-- Evaluation commutes with the original coefficient-algebra maps. -/
theorem evaluationCoefficientMap_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of K)} (a : R ⟶ R') :
    CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := K) K
        (a.hom.restrictScalars k)) ≫ evaluationCoefficientMap k K R' =
      evaluationCoefficientMap k K R ≫ a := by
  apply CommAlgCat.hom_ext
  ext r
  simp [evaluationCoefficientMap, Algebra.smul_def]

variable [Module.Finite k K] [Module.Projective k K]
    (H : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance evaluationSource_isAffine :
    IsAffine ((GroupScheme.baseChange (algebraBaseMap k K)).obj
      (groupScheme k K H)).X.left := by
  change IsAffine (pullback (groupScheme k K H).X.hom (algebraBaseMap k K))
  infer_instance

/-- The original tensor-valued point evaluated by scalar multiplication. -/
def evaluationPointHom (R : CommAlgCat.{u} (CommRingCat.of K)) :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj
      (groupScheme k K H)).affinePoints R →* H.affinePoints R :=
  (H.affinePointMap (evaluationCoefficientMap k K R)).comp
    (baseChangeTensorPointsEquiv k K K H R).toMonoidHom

/-- Evaluation is natural on every affine test algebra. -/
theorem evaluationPointHom_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of K)} (a : R ⟶ R')
    (p : ((GroupScheme.baseChange (algebraBaseMap k K)).obj
      (groupScheme k K H)).affinePoints R) :
    evaluationPointHom k K H R'
        (((GroupScheme.baseChange (algebraBaseMap k K)).obj
          (groupScheme k K H)).affinePointMap a p) =
      H.affinePointMap a (evaluationPointHom k K H R p) := by
  change H.affinePointMap _ (baseChangeTensorPointsEquiv k K K H R' _) = _
  rw [baseChangeTensorPointsEquiv_naturality]
  change H.affinePointMap _ (H.affinePointMap _ _) =
    H.affinePointMap a (H.affinePointMap _ _)
  rw [← MonoidHom.comp_apply, ← affinePointMap_comp,
    evaluationCoefficientMap_naturality, affinePointMap_comp]
  rfl

/-- Evaluation as a natural transformation of the actual affine point functors. -/
def evaluationTransformation :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj
      (groupScheme k K H)).affinePointFunctor ⟶ H.affinePointFunctor where
  app R := GrpCat.ofHom (evaluationPointHom k K H R)
  naturality R R' a := by
    ext p
    exact evaluationPointHom_naturality k K H a p

/-- The actual evaluation homomorphism from scalar-extended Weil restriction. -/
def evaluation :
    (GroupScheme.baseChange (algebraBaseMap k K)).obj
      (groupScheme k K H) ⟶ H :=
  AffinePointComparison.map (evaluationTransformation k K H)

/-- The actual evaluation retains the original tensor-valued point formula. -/
theorem evaluation_affinePoints
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (p : ((GroupScheme.baseChange (algebraBaseMap k K)).obj
      (groupScheme k K H)).affinePoints R) :
    p ≫ (evaluation k K H).hom.hom =
      H.affinePointMap (evaluationCoefficientMap k K R)
        (baseChangeTensorPointsEquiv k K K H R p) :=
  AffinePointComparison.map_points (evaluationTransformation k K H) R p

end Langlands.GroupScheme.AffineWeil
