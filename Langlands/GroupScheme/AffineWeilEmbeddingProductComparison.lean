import Langlands.GroupScheme.AffineWeilEmbeddingProductPoints

/-! # The actual embedding-product splitting of affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

open Langlands.Algebra.SeparableTensor
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (k K Ω : Type u) [CommRing k] [CommRing K] [CommRing Ω]
  [Algebra k K] [Algebra k Ω]

/-- The actual conjugate factor, using precisely the given embedding on the base. -/
abbrev embeddingFactor (H : GroupScheme (Spec (CommRingCat.of K))) (τ : K →ₐ[k] Ω) :=
  (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H

/-- The scalar-restricted affine test is the test with its specified conjugate K-action. -/
def embeddingTestIso (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω) :
    (Over.map (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj
        ((algSpec (CommRingCat.of Ω)).obj (op R)) ≅
      (algSpec (CommRingCat.of K)).obj (op (embeddingCoefficientAlgebra k K Ω R τ)) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of R))) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap Ω R).comp τ.toRingHom)) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω R)) ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom)
    rw [Category.id_comp, ← Spec.map_comp]
    rfl)

variable (H : GroupScheme (Spec (CommRingCat.of K)))

/-- Actual factor points, compared multiplicatively with the original conjugate-coefficient points. -/
def embeddingFactorPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (τ : K →ₐ[k] Ω) :
    (embeddingFactor k K Ω H τ).affinePoints R ≃*
      H.affinePoints (embeddingCoefficientAlgebra k K Ω R τ) :=
  (baseChangePointsEquiv (Spec.map (CommRingCat.ofHom τ.toRingHom)) H
    ((algSpec (CommRingCat.of Ω)).obj (op R))).trans
      (H.points.mapIso (embeddingTestIso k K Ω R τ).symm.op).groupIsoToMulEquiv

/-- The factor point is the original first projection from the actual pullback. -/
@[simp] theorem embeddingFactorPointsEquiv_left
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : (embeddingFactor k K Ω H τ).affinePoints R) :
    (embeddingFactorPointsEquiv k K Ω H R τ p).left =
      p.left ≫ pullback.fst H.X.hom (Spec.map (CommRingCat.ofHom τ.toRingHom)) := by
  change 𝟙 _ ≫ (p.left ≫ _) = _
  exact Category.id_comp _

/-- This factor comparison is natural in the coefficient algebra. -/
theorem embeddingFactorPointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of Ω)} (a : R ⟶ R') (τ : K →ₐ[k] Ω)
    (p : (embeddingFactor k K Ω H τ).affinePoints R) :
    embeddingFactorPointsEquiv k K Ω H R' τ
        ((embeddingFactor k K Ω H τ).affinePointMap a p) =
      H.affinePointMap (embeddingCoefficientMap k K Ω a τ)
        (embeddingFactorPointsEquiv k K Ω H R τ p) := by
  apply Over.OverMorphism.ext
  rw [embeddingFactorPointsEquiv_left]
  change (Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ p.left) ≫ _ =
    Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫
      (embeddingFactorPointsEquiv k K Ω H R τ p).left
  rw [embeddingFactorPointsEquiv_left, Category.assoc]

/-- This factor comparison retains the original target homomorphism. -/
theorem embeddingFactorPointsEquiv_target
    {H' : GroupScheme (Spec (CommRingCat.of K))} (f : H ⟶ H')
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : (embeddingFactor k K Ω H τ).affinePoints R) :
    embeddingFactorPointsEquiv k K Ω H' R τ
        (p ≫ ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom τ.toRingHom))).map f).hom.hom) =
      embeddingFactorPointsEquiv k K Ω H R τ p ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  rw [embeddingFactorPointsEquiv_left]
  change (p.left ≫ ((Over.pullback
    (Spec.map (CommRingCat.ofHom τ.toRingHom))).map f.hom.hom).left) ≫ _ = _
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, ← embeddingFactorPointsEquiv_left]
  rfl

attribute [local instance] coefficientBaseAlgebra coefficientScalarTower

variable [Module.Finite k K] [Module.Projective k K]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- Original tensor-valued points of the actual base-changed Weil restriction. -/
def baseChangeTensorPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of Ω)) :
    ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj (groupScheme k K H)).affinePoints R ≃*
      H.affinePoints (CommAlgCat.of K (K ⊗[k] R)) :=
  (affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H)).symm.trans
    (pointsEquiv k K H R)

/-- The original tensor-valued point comparison is natural in coefficients. -/
theorem baseChangeTensorPointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of Ω)} (a : R ⟶ R')
    (p : ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj
      (groupScheme k K H)).affinePoints R) :
    baseChangeTensorPointsEquiv k K Ω H R'
        (((GroupScheme.baseChange (algebraBaseMap k Ω)).obj
          (groupScheme k K H)).affinePointMap a p) =
      H.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := K) K (a.hom.restrictScalars k)))
        (baseChangeTensorPointsEquiv k K Ω H R p) := by
  have hc : (affinePointsBaseChangeMulEquiv k Ω R' (groupScheme k K H)).symm
      (((GroupScheme.baseChange (algebraBaseMap k Ω)).obj
        (groupScheme k K H)).affinePointMap a p) =
      (groupScheme k K H).affinePointMap (CommAlgCat.ofHom (a.hom.restrictScalars k))
        ((affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H)).symm p) := by
    apply (affinePointsBaseChangeMulEquiv k Ω R' (groupScheme k K H)).injective
    rw [MulEquiv.apply_symm_apply, ← affinePointsBaseChangeMulEquiv_naturality,
      MulEquiv.apply_symm_apply]
    rfl
  change pointsEquiv k K H R'
      ((affinePointsBaseChangeMulEquiv k Ω R' (groupScheme k K H)).symm
        (((GroupScheme.baseChange (algebraBaseMap k Ω)).obj
          (groupScheme k K H)).affinePointMap a p)) =
    H.affinePointMap _ (pointsEquiv k K H R
      ((affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H)).symm p))
  rw [hc, pointsEquiv_naturality]

end Langlands.GroupScheme.AffineWeil
