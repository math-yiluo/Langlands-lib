import Langlands.GroupScheme.AffineWeilEmbeddingEvaluation

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct
namespace Langlands.GroupScheme.AffineWeil
open Langlands.Algebra.SeparableTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
set_option maxRecDepth 4000
variable (k K Ω : Type u) [CommRing k] [CommRing K] [CommRing Ω]
  [Algebra k K] [Algebra k Ω] [Finite (K →ₐ[k] Ω)]
  (hsplit : Function.Bijective (embeddingEvaluation k K Ω))
  [Module.Finite k K] [Module.Projective k K]
  (H : GroupScheme (Spec (CommRingCat.of K)))
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
attribute [local instance] coefficientBaseAlgebra coefficientScalarTower

/-- The original coordinate composition retains its underlying over-base map. -/
theorem embeddingProductIsoOfBijective_comp_hom_hom (τ : K →ₐ[k] Ω) :
    ((embeddingProductIsoOfBijective k K Ω hsplit H).hom ≫
      Pi.π (embeddingFactor k K Ω H) τ).hom.hom =
    (embeddingProductIsoOfBijective k K Ω hsplit H).hom.hom.hom ≫
      (Pi.π (embeddingFactor k K Ω H) τ).hom.hom := rfl

omit [Finite (K →ₐ[k] Ω)] [Module.Finite k K] [Module.Projective k K]
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
/-- The factor comparison detects equality without reducing the tested points. -/
theorem embeddingFactorPointsEquiv_injective
    (R : CommAlgCat.{u} (CommRingCat.of Ω)) (τ : K →ₐ[k] Ω)
    (x y : (embeddingFactor k K Ω H τ).affinePoints R)
    (h : embeddingFactorPointsEquiv k K Ω H R τ x =
      embeddingFactorPointsEquiv k K Ω H R τ y) : x = y :=
  (embeddingFactorPointsEquiv k K Ω H R τ).injective h


/-- The original embedding coordinate, with its point type explicitly retained. -/
def embeddingProductCoordinatePoint
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    (embeddingFactor k K Ω H τ).affinePoints R :=
  piPointsEquiv (embeddingFactor k K Ω H) ((algSpec (CommRingCat.of Ω)).obj (op R))
    (p ≫ (embeddingProductIsoOfBijective k K Ω hsplit H).hom.hom.hom) τ

/-- The pullback evaluation coordinate, retaining the same explicit point type. -/
def embeddingEvaluationPoint
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    (embeddingFactor k K Ω H τ).affinePoints R :=
  p ≫ (EmbeddingProduct.evaluationComponent (algebraBaseMap k K)
    (algebraBaseMap k Ω) (Spec.map (CommRingCat.ofHom τ.toRingHom))
    (embeddingBaseMap_over k K Ω τ) (groupScheme k K H) H
    (evaluation k K H)).hom.hom

/-- The named original and pullback coordinates have the same factor comparison. -/
theorem embeddingProductCoordinatePoint_compared
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    embeddingFactorPointsEquiv k K Ω H R τ
        (embeddingProductCoordinatePoint k K Ω hsplit H R p τ) =
      embeddingFactorPointsEquiv k K Ω H R τ
        (embeddingEvaluationPoint k K Ω H R p τ) :=
  embeddingProductIsoOfBijective_component_points k K Ω hsplit H R p τ

/-- The named coordinates agree as original points of the pullback. -/
theorem embeddingProductCoordinatePoint_eq
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    embeddingProductCoordinatePoint k K Ω hsplit H R p τ =
      embeddingEvaluationPoint k K Ω H R p τ :=
  embeddingFactorPointsEquiv_injective k K Ω H R τ
    (embeddingProductCoordinatePoint k K Ω hsplit H R p τ)
    (embeddingEvaluationPoint k K Ω H R p τ)
    (embeddingProductCoordinatePoint_compared k K Ω hsplit H R p τ)

/-- The underlying original product coordinate, with explicit over-base endpoints. -/
def embeddingProductCoordinateOverHom (τ : K →ₐ[k] Ω) :
    (embeddingRestrictionBaseChange k K Ω H).X ⟶ (embeddingFactor k K Ω H τ).X :=
  (embeddingProductIsoOfBijective k K Ω hsplit H).hom.hom.hom ≫
    (Pi.π (embeddingFactor k K Ω H) τ).hom.hom

/-- The underlying pullback evaluation, with explicit over-base endpoints. -/
def embeddingEvaluationOverHom (τ : K →ₐ[k] Ω) :
    (embeddingRestrictionBaseChange k K Ω H).X ⟶ (embeddingFactor k K Ω H τ).X :=
  (EmbeddingProduct.evaluationComponent (algebraBaseMap k K) (algebraBaseMap k Ω)
    (Spec.map (CommRingCat.ofHom τ.toRingHom)) (embeddingBaseMap_over k K Ω τ)
    (groupScheme k K H) H (evaluation k K H)).hom.hom

/-- The named underlying product coordinate is its original composite. -/
theorem embeddingProductCoordinateOverHom_eq (τ : K →ₐ[k] Ω) :
    embeddingProductCoordinateOverHom k K Ω hsplit H τ =
      (embeddingProductIsoOfBijective k K Ω hsplit H).hom.hom.hom ≫
        (Pi.π (embeddingFactor k K Ω H) τ).hom.hom := rfl

omit [Finite (K →ₐ[k] Ω)] in
/-- The named underlying evaluation is the original pullback morphism. -/
theorem embeddingEvaluationOverHom_eq (τ : K →ₐ[k] Ω) :
    embeddingEvaluationOverHom k K Ω H τ =
      (EmbeddingProduct.evaluationComponent (algebraBaseMap k K) (algebraBaseMap k Ω)
        (Spec.map (CommRingCat.ofHom τ.toRingHom)) (embeddingBaseMap_over k K Ω τ)
        (groupScheme k K H) H (evaluation k K H)).hom.hom := rfl

/-- Applying the named underlying product coordinate gives the named point. -/
theorem embeddingProductCoordinateOverHom_points
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    p ≫ embeddingProductCoordinateOverHom k K Ω hsplit H τ =
      embeddingProductCoordinatePoint k K Ω hsplit H R p τ := by
  exact (congrArg (fun f => p ≫ f)
    (embeddingProductCoordinateOverHom_eq k K Ω hsplit H τ)).trans
      (Category.assoc p _ _).symm

omit [Finite (K →ₐ[k] Ω)] in
/-- Applying the named underlying evaluation gives the named point. -/
theorem embeddingEvaluationOverHom_points
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    p ≫ embeddingEvaluationOverHom k K Ω H τ =
      embeddingEvaluationPoint k K Ω H R p τ :=
  congrArg (fun f => p ≫ f) (embeddingEvaluationOverHom_eq k K Ω H τ)

/-- The two underlying coordinate maps agree on every affine test. -/
theorem embeddingProductCoordinateOverHom_points_eq
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    p ≫ embeddingProductCoordinateOverHom k K Ω hsplit H τ =
      p ≫ embeddingEvaluationOverHom k K Ω H τ :=
  (embeddingProductCoordinateOverHom_points k K Ω hsplit H R p τ).trans
    ((embeddingProductCoordinatePoint_eq k K Ω hsplit H R p τ).trans
      (embeddingEvaluationOverHom_points k K Ω H R p τ).symm)

/-- The original underlying coordinate map equals actual pullback evaluation. -/
theorem embeddingProductCoordinateOverHom_eq_evaluation (τ : K →ₐ[k] Ω) :
    embeddingProductCoordinateOverHom k K Ω hsplit H τ =
      embeddingEvaluationOverHom k K Ω H τ := by
  apply (cancel_epi (AffinePointComparison.presentation
    (embeddingRestrictionBaseChange k K Ω H)).hom).mp
  exact embeddingProductCoordinateOverHom_points_eq k K Ω hsplit H _ _ τ

/-- Every original tensor-product coordinate is the actual pullback of scalar evaluation. -/
theorem embeddingProductIsoOfBijective_hom_π (τ : K →ₐ[k] Ω) :
    (embeddingProductIsoOfBijective k K Ω hsplit H).hom ≫
        Pi.π (embeddingFactor k K Ω H) τ =
      EmbeddingProduct.evaluationComponent (algebraBaseMap k K) (algebraBaseMap k Ω)
        (Spec.map (CommRingCat.ofHom τ.toRingHom)) (embeddingBaseMap_over k K Ω τ)
        (groupScheme k K H) H (evaluation k K H) := by
  apply Grp.hom_ext
  exact (embeddingProductIsoOfBijective_comp_hom_hom k K Ω hsplit H τ).trans
    ((embeddingProductCoordinateOverHom_eq k K Ω hsplit H τ).symm.trans
      ((embeddingProductCoordinateOverHom_eq_evaluation k K Ω hsplit H τ).trans
        (embeddingEvaluationOverHom_eq k K Ω H τ)))

end Langlands.GroupScheme.AffineWeil
