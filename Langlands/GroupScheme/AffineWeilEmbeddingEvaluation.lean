import Langlands.GroupScheme.EmbeddingEvaluationCoherence
import Langlands.GroupScheme.AffineWeilEvaluation
import Langlands.GroupScheme.AffineWeilEmbeddingProduct

/-! # Original Weil-product coordinates are pullbacks of evaluation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

open Langlands.Algebra.SeparableTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable (k K Ω : Type u) [CommRing k] [CommRing K] [CommRing Ω]
  [Algebra k K] [Algebra k Ω]

attribute [local instance] coefficientBaseAlgebra coefficientScalarTower

/-- The identity coefficient map retains the common original k-action. -/
def embeddingCoefficientRestriction
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω) :
    CommAlgCat.of k R ⟶ CommAlgCat.of k (embeddingCoefficientAlgebra k K Ω R τ) :=
  CommAlgCat.ofHom {
    toRingHom := RingHom.id R
    commutes' r := by
      change algebraMap Ω R (algebraMap k Ω r) =
        algebraMap Ω R (τ (algebraMap k K r))
      rw [τ.commutes] }

@[simp] theorem embeddingCoefficientRestriction_apply
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω) (r : R) :
    (embeddingCoefficientRestriction k K Ω R τ).hom r = r := rfl

variable [Finite (K →ₐ[k] Ω)]
  (hsplit : Function.Bijective (embeddingEvaluation k K Ω))

/-- Restriction followed by scalar multiplication is the original tensor evaluation. -/
theorem embeddingCoefficientRestriction_evaluation
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω) :
    CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := K) K
        (embeddingCoefficientRestriction k K Ω R τ).hom) ≫
      evaluationCoefficientMap k K (embeddingCoefficientAlgebra k K Ω R τ) =
        tensorEmbeddingEvaluationMap k K Ω hsplit R τ := by
  apply CommAlgCat.hom_ext
  ext r
  change (evaluationCoefficientMap k K
      (embeddingCoefficientAlgebra k K Ω R τ)).hom (1 ⊗ₜ[k] r) =
    tensorEmbeddingEvaluation k K Ω hsplit R τ (1 ⊗ₜ[k] r)
  simp [evaluationCoefficientMap, Algebra.smul_def]

omit [Finite (K →ₐ[k] Ω)] in
/-- Every original embedding gives a map of spectra over the original base. -/
theorem embeddingBaseMap_over (τ : K →ₐ[k] Ω) :
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ algebraBaseMap k K =
      algebraBaseMap k Ω := by
  unfold algebraBaseMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact τ.commutes

/-- The point of the intermediate scalar extension over conjugate coefficients. -/
def embeddingIntermediatePoint (W : GroupScheme (Spec (CommRingCat.of k)))
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj W).affinePoints R) :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj W).affinePoints
      (embeddingCoefficientAlgebra k K Ω R τ) :=
  Over.homMk (p.left ≫ EmbeddingProduct.intermediateProjection (algebraBaseMap k K)
    (algebraBaseMap k Ω) (Spec.map (CommRingCat.ofHom τ.toRingHom))
    (embeddingBaseMap_over k K Ω τ) W) (by
      change (p.left ≫ _) ≫ pullback.snd W.X.hom (algebraBaseMap k K) = _
      rw [Category.assoc, EmbeddingProduct.intermediateProjection_snd, ← Category.assoc]
      have hp : p.left ≫ pullback.snd W.X.hom (algebraBaseMap k Ω) =
        ((algSpec (CommRingCat.of Ω)).obj (op R)).hom := Over.w p
      rw [hp]
      change Spec.map (CommRingCat.ofHom (algebraMap Ω R)) ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom) =
          Spec.map (CommRingCat.ofHom ((algebraMap Ω R).comp τ.toRingHom))
      rw [← Spec.map_comp]
      rfl)

omit [Finite (K →ₐ[k] Ω)] in
/-- Its underlying map is the original intermediate pullback projection. -/
theorem embeddingIntermediatePoint_left
    (W : GroupScheme (Spec (CommRingCat.of k)))
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj W).affinePoints R) :
    (embeddingIntermediatePoint k K Ω W R τ p).left =
      p.left ≫ EmbeddingProduct.intermediateProjection (algebraBaseMap k K)
        (algebraBaseMap k Ω) (Spec.map (CommRingCat.ofHom τ.toRingHom))
        (embeddingBaseMap_over k K Ω τ) W := rfl

omit [Finite (K →ₐ[k] Ω)] in
/-- Forgetting the intermediate scalar extension retains the original point. -/
theorem embeddingIntermediatePoint_restriction
    (W : GroupScheme (Spec (CommRingCat.of k)))
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj W).affinePoints R) :
    (affinePointsBaseChangeMulEquiv k K (embeddingCoefficientAlgebra k K Ω R τ) W).symm
        (embeddingIntermediatePoint k K Ω W R τ p) =
      W.affinePointMap (embeddingCoefficientRestriction k K Ω R τ)
        ((affinePointsBaseChangeMulEquiv k Ω R W).symm p) := by
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left, embeddingIntermediatePoint_left]
  change (p.left ≫ _) ≫ pullback.fst W.X.hom (algebraBaseMap k K) =
    Spec.map (𝟙 (CommRingCat.of R)) ≫
      ((affinePointsBaseChangeMulEquiv k Ω R W).symm p).left
  rw [Category.assoc, EmbeddingProduct.intermediateProjection_fst,
    Spec.map_id, Category.id_comp, affinePointsBaseChangeMulEquiv_symm_left]

omit [Finite (K →ₐ[k] Ω)] in
/-- The pullback component gives the original intermediate point followed by evaluation. -/
theorem evaluationComponent_embeddingPoints
    (W : GroupScheme (Spec (CommRingCat.of k)))
    (H : GroupScheme (Spec (CommRingCat.of K)))
    (e : (GroupScheme.baseChange (algebraBaseMap k K)).obj W ⟶ H)
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj W).affinePoints R) :
    embeddingFactorPointsEquiv k K Ω H R τ
        (p ≫ (EmbeddingProduct.evaluationComponent (algebraBaseMap k K)
          (algebraBaseMap k Ω) (Spec.map (CommRingCat.ofHom τ.toRingHom))
          (embeddingBaseMap_over k K Ω τ) W H e).hom.hom) =
      embeddingIntermediatePoint k K Ω W R τ p ≫ e.hom.hom := by
  apply Over.OverMorphism.ext
  rw [embeddingFactorPointsEquiv_left]
  change (p.left ≫ _) ≫ pullback.fst H.X.hom
      (Spec.map (CommRingCat.ofHom τ.toRingHom)) =
    (embeddingIntermediatePoint k K Ω W R τ p).left ≫ e.hom.hom.left
  rw [Category.assoc, EmbeddingProduct.evaluationComponent_fst,
    embeddingIntermediatePoint_left, Category.assoc]

/-- A factor coordinate equality can be checked before specializing its source or maps. -/
theorem embeddingFactor_component_eq
    (W : GroupScheme (Spec (CommRingCat.of Ω))) [IsAffine W.X.left]
    (H : GroupScheme (Spec (CommRingCat.of K))) (τ : K →ₐ[k] Ω)
    (f : W ⟶ pi (embeddingFactor k K Ω H)) (g : W ⟶ embeddingFactor k K Ω H τ)
    (h : ∀ (R : CommAlgCat.{u} (CommRingCat.of Ω)) (p : W.affinePoints R),
      embeddingFactorPointsEquiv k K Ω H R τ
        (piPointsEquiv (embeddingFactor k K Ω H)
          ((algSpec (CommRingCat.of Ω)).obj (op R)) (p ≫ f.hom.hom) τ) =
      embeddingFactorPointsEquiv k K Ω H R τ (p ≫ g.hom.hom)) :
    f ≫ Pi.π (embeddingFactor k K Ω H) τ = g := by
  apply AffinePointComparison.hom_ext W
  intro R p
  apply (embeddingFactorPointsEquiv k K Ω H R τ).injective
  simpa only [Grp.comp_hom_hom, piPointsEquiv_apply, Category.assoc] using h R p

variable [Module.Finite k K] [Module.Projective k K]
    (H : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

omit [Finite (K →ₐ[k] Ω)] in
/-- The original intermediate tensor point is restriction of the original upper-field tensor point. -/
theorem embeddingIntermediatePoint_tensor
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) :
    baseChangeTensorPointsEquiv k K K H (embeddingCoefficientAlgebra k K Ω R τ)
        (embeddingIntermediatePoint k K Ω (groupScheme k K H) R τ p) =
      H.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := K) K
        (embeddingCoefficientRestriction k K Ω R τ).hom))
        (baseChangeTensorPointsEquiv k K Ω H R p) := by
  exact (congrArg (pointsEquiv k K H (embeddingCoefficientAlgebra k K Ω R τ))
      (embeddingIntermediatePoint_restriction k K Ω (groupScheme k K H) R τ p)).trans
    (pointsEquiv_naturality k K H (embeddingCoefficientRestriction k K Ω R τ).hom
      ((affinePointsBaseChangeMulEquiv k Ω R (groupScheme k K H)).symm p))

omit [Module.Finite k K] [Module.Projective k K] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] in
/-- Composition of coefficient restriction with evaluation on any original tensor point. -/
theorem embeddingCoefficientRestriction_evaluation_points
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (x : H.affinePoints (CommAlgCat.of K (K ⊗[k] R))) :
    H.affinePointMap (evaluationCoefficientMap k K (embeddingCoefficientAlgebra k K Ω R τ))
        (H.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := K) K
          (embeddingCoefficientRestriction k K Ω R τ).hom)) x) =
      H.affinePointMap (tensorEmbeddingEvaluationMap k K Ω hsplit R τ) x := by
  rw [← MonoidHom.comp_apply, ← affinePointMap_comp,
    embeddingCoefficientRestriction_evaluation]

set_option maxHeartbeats 50000 in
/-- Evaluating the original intermediate tensor point gives embedding evaluation. -/
theorem embeddingIntermediatePoint_evaluation
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) :
    H.affinePointMap (evaluationCoefficientMap k K (embeddingCoefficientAlgebra k K Ω R τ))
        (baseChangeTensorPointsEquiv k K K H (embeddingCoefficientAlgebra k K Ω R τ)
          (embeddingIntermediatePoint k K Ω (groupScheme k K H) R τ p)) =
      H.affinePointMap (tensorEmbeddingEvaluationMap k K Ω hsplit R τ)
        (baseChangeTensorPointsEquiv k K Ω H R p) := by
  exact (congrArg
    (H.affinePointMap (evaluationCoefficientMap k K (embeddingCoefficientAlgebra k K Ω R τ)))
    (embeddingIntermediatePoint_tensor k K Ω H R τ p)).trans
      (embeddingCoefficientRestriction_evaluation_points k K Ω hsplit H R τ
        (baseChangeTensorPointsEquiv k K Ω H R p))

omit [Finite (K →ₐ[k] Ω)] in
set_option maxHeartbeats 50000 in
/-- The actual Weil pullback component is scalar evaluation of the intermediate point. -/
theorem evaluationComponent_intermediatePoint
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) :
    embeddingFactorPointsEquiv k K Ω H R τ
        (p ≫ (EmbeddingProduct.evaluationComponent (algebraBaseMap k K)
          (algebraBaseMap k Ω) (Spec.map (CommRingCat.ofHom τ.toRingHom))
          (embeddingBaseMap_over k K Ω τ) (groupScheme k K H) H
          (evaluation k K H)).hom.hom) =
      embeddingIntermediatePoint k K Ω (groupScheme k K H) R τ p ≫
        (evaluation k K H).hom.hom := by
  apply Over.OverMorphism.ext
  rw [embeddingFactorPointsEquiv_left]
  change (p.left ≫ _) ≫ pullback.fst H.X.hom
      (Spec.map (CommRingCat.ofHom τ.toRingHom)) =
    (embeddingIntermediatePoint k K Ω (groupScheme k K H) R τ p).left ≫
      (evaluation k K H).hom.hom.left
  rw [Category.assoc, EmbeddingProduct.evaluationComponent_fst,
    embeddingIntermediatePoint_left, Category.assoc]

omit [Finite (K →ₐ[k] Ω)] in
set_option maxHeartbeats 50000 in
/-- Scalar evaluation of the intermediate point has the original multiplication formula. -/
theorem evaluation_intermediatePoint
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) :
    embeddingIntermediatePoint k K Ω (groupScheme k K H) R τ p ≫
        (evaluation k K H).hom.hom =
      H.affinePointMap (evaluationCoefficientMap k K (embeddingCoefficientAlgebra k K Ω R τ))
        (baseChangeTensorPointsEquiv k K K H (embeddingCoefficientAlgebra k K Ω R τ)
          (embeddingIntermediatePoint k K Ω (groupScheme k K H) R τ p)) :=
  evaluation_affinePoints k K H (embeddingCoefficientAlgebra k K Ω R τ)
    (embeddingIntermediatePoint k K Ω (groupScheme k K H) R τ p)

set_option maxHeartbeats 50000 in
/-- Evaluation of the intermediate point is the original embedding evaluation. -/
theorem evaluationComponent_embeddingEvaluationPoints
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) :
    embeddingFactorPointsEquiv k K Ω H R τ
        (p ≫ (EmbeddingProduct.evaluationComponent (algebraBaseMap k K)
          (algebraBaseMap k Ω) (Spec.map (CommRingCat.ofHom τ.toRingHom))
          (embeddingBaseMap_over k K Ω τ) (groupScheme k K H) H
          (evaluation k K H)).hom.hom) =
      H.affinePointMap (tensorEmbeddingEvaluationMap k K Ω hsplit R τ)
        (baseChangeTensorPointsEquiv k K Ω H R p) :=
  (evaluationComponent_intermediatePoint k K Ω H R τ p).trans
    ((evaluation_intermediatePoint k K Ω H R τ p).trans
      (embeddingIntermediatePoint_evaluation k K Ω hsplit H R τ p))

set_option maxHeartbeats 50000 in
/-- The original product and evaluation pullback have identical affine coordinates. -/
theorem embeddingProductIsoOfBijective_component_points
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    embeddingFactorPointsEquiv k K Ω H R τ
        (piPointsEquiv (embeddingFactor k K Ω H)
          ((algSpec (CommRingCat.of Ω)).obj (op R))
          (p ≫ (embeddingProductIsoOfBijective k K Ω hsplit H).hom.hom.hom) τ) =
      embeddingFactorPointsEquiv k K Ω H R τ
        (p ≫ (EmbeddingProduct.evaluationComponent (algebraBaseMap k K)
          (algebraBaseMap k Ω) (Spec.map (CommRingCat.ofHom τ.toRingHom))
          (embeddingBaseMap_over k K Ω τ) (groupScheme k K H) H
          (evaluation k K H)).hom.hom) :=
  (embeddingProductIsoOfBijective_coordinate k K Ω hsplit H R p τ).trans
    (evaluationComponent_embeddingEvaluationPoints k K Ω hsplit H R τ p).symm

end Langlands.GroupScheme.AffineWeil
