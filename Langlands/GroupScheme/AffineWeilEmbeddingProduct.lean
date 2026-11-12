import Langlands.GroupScheme.AffineWeilEmbeddingProductTargets
import Langlands.GroupScheme.AffinePointComparison
import Langlands.Algebra.SeparableTensorProof

/-! # The actual embedding-product isomorphism for affine Weil restriction -/

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
set_option maxRecDepth 4000

section Rings

variable (k K Ω : Type u) [CommRing k] [CommRing K] [CommRing Ω]
  [Algebra k K] [Algebra k Ω] [Module.Finite k K] [Module.Projective k K]
  [Finite (K →ₐ[k] Ω)]
  (hsplit : Function.Bijective (embeddingEvaluation k K Ω))
  (H : GroupScheme (Spec (CommRingCat.of K)))
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

attribute [local instance] coefficientBaseAlgebra coefficientScalarTower

/-- The original Weil group after the actual extension of its base. -/
abbrev embeddingRestrictionBaseChange : GroupScheme (Spec (CommRingCat.of Ω)) :=
  (GroupScheme.baseChange (algebraBaseMap k Ω)).obj (groupScheme k K H)

/-- The actual categorical product of the embedding base changes. -/
abbrev embeddingProduct : GroupScheme (Spec (CommRingCat.of Ω)) :=
  GroupScheme.pi (embeddingFactor k K Ω H)

/-- Canonical multiplicative splitting on every actual affine test. -/
def embeddingProductPointEquiv (R : CommAlgCat.{u} (CommRingCat.of Ω)) :
    (embeddingRestrictionBaseChange k K Ω H).affinePoints R ≃*
      (embeddingProduct k K Ω H).affinePoints R :=
  (baseChangeTensorPointsEquiv k K Ω H R).trans <|
    (tensorEmbeddingPointsEquiv k K Ω hsplit H R).trans <|
      (MulEquiv.piCongrRight (fun τ =>
        (embeddingFactorPointsEquiv k K Ω H R τ).symm)).trans
        (piPointsEquiv (embeddingFactor k K Ω H)
          ((algSpec (CommRingCat.of Ω)).obj (op R))).symm

/-- Projection to a factor is exactly the original tensor-point evaluation. -/
theorem embeddingProductPointEquiv_component
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    embeddingFactorPointsEquiv k K Ω H R τ
        (piPointsEquiv (embeddingFactor k K Ω H)
          ((algSpec (CommRingCat.of Ω)).obj (op R))
          (embeddingProductPointEquiv k K Ω hsplit H R p) τ) =
      tensorEmbeddingPointsEquiv k K Ω hsplit H R
        (baseChangeTensorPointsEquiv k K Ω H R p) τ := by
  simp only [embeddingProductPointEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, MulEquiv.piCongrRight_apply]

/-- Naturality of the splitting on actual coefficient points. -/
theorem embeddingProductPointEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of Ω)} (a : R ⟶ R')
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) :
    embeddingProductPointEquiv k K Ω hsplit H R'
        ((embeddingRestrictionBaseChange k K Ω H).affinePointMap a p) =
      (embeddingProduct k K Ω H).affinePointMap a
        (embeddingProductPointEquiv k K Ω hsplit H R p) := by
  apply (piPointsEquiv (embeddingFactor k K Ω H)
    ((algSpec (CommRingCat.of Ω)).obj (op R'))).injective
  funext τ
  apply (embeddingFactorPointsEquiv k K Ω H R' τ).injective
  rw [embeddingProductPointEquiv_component]
  have ht := congrFun (piPointsEquiv_naturality (embeddingFactor k K Ω H)
    ((algSpec (CommRingCat.of Ω)).map a.op)
    (embeddingProductPointEquiv k K Ω hsplit H R p)) τ
  change piPointsEquiv (embeddingFactor k K Ω H)
      ((algSpec (CommRingCat.of Ω)).obj (op R'))
      ((embeddingProduct k K Ω H).affinePointMap a
        (embeddingProductPointEquiv k K Ω hsplit H R p)) τ =
    (embeddingFactor k K Ω H τ).affinePointMap a
      (piPointsEquiv (embeddingFactor k K Ω H)
        ((algSpec (CommRingCat.of Ω)).obj (op R))
        (embeddingProductPointEquiv k K Ω hsplit H R p) τ) at ht
  rw [ht, embeddingFactorPointsEquiv_naturality,
    embeddingProductPointEquiv_component, baseChangeTensorPointsEquiv_naturality,
    tensorEmbeddingPointsEquiv_naturality]

/-- The actual affine group-valued point functors are naturally isomorphic. -/
def embeddingProductAffinePointIso :
    (embeddingRestrictionBaseChange k K Ω H).affinePointFunctor ≅
      (embeddingProduct k K Ω H).affinePointFunctor :=
  NatIso.ofComponents
    (fun R => (embeddingProductPointEquiv k K Ω hsplit H R).toGrpIso) (by
      intro R R' a
      ext p
      exact embeddingProductPointEquiv_naturality k K Ω hsplit H a p)

/-- Actual group-scheme splitting for a bijective canonical embedding evaluation. -/
def embeddingProductIsoOfBijective :
    embeddingRestrictionBaseChange k K Ω H ≅ embeddingProduct k K Ω H :=
  AffinePointComparison.iso (embeddingProductAffinePointIso k K Ω hsplit H)

/-- The reconstructed isomorphism induces precisely the original point splitting. -/
theorem embeddingProductIsoOfBijective_hom_points
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) :
    p ≫ (embeddingProductIsoOfBijective k K Ω hsplit H).hom.hom.hom =
      embeddingProductPointEquiv k K Ω hsplit H R p :=
  AffinePointComparison.iso_hom_points (embeddingProductAffinePointIso k K Ω hsplit H) R p

/-- Scheme-valued coordinates are the original tensor-valued point followed by evaluation. -/
theorem embeddingProductIsoOfBijective_coordinate
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    embeddingFactorPointsEquiv k K Ω H R τ
        (piPointsEquiv (embeddingFactor k K Ω H)
          ((algSpec (CommRingCat.of Ω)).obj (op R))
          (p ≫ (embeddingProductIsoOfBijective k K Ω hsplit H).hom.hom.hom) τ) =
      H.affinePointMap (tensorEmbeddingEvaluationMap k K Ω hsplit R τ)
        (baseChangeTensorPointsEquiv k K Ω H R p) := by
  rw [embeddingProductIsoOfBijective_hom_points,
    embeddingProductPointEquiv_component, tensorEmbeddingPointsEquiv_apply]

/-- In global-section coordinates, every component is exactly tensorEmbeddingEvaluation. -/
theorem embeddingProductIsoOfBijective_coordinates
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    (affineSchemePointEquiv K H.X (embeddingCoefficientAlgebra k K Ω R τ)
      (embeddingFactorPointsEquiv k K Ω H R τ
        (piPointsEquiv (embeddingFactor k K Ω H)
          ((algSpec (CommRingCat.of Ω)).obj (op R))
          (p ≫ (embeddingProductIsoOfBijective k K Ω hsplit H).hom.hom.hom) τ))).toAlgHom.toRingHom =
      (tensorEmbeddingEvaluation k K Ω hsplit R τ).comp
        (affineSchemePointEquiv K H.X (K ⊗[k] R)
          (baseChangeTensorPointsEquiv k K Ω H R p)).toAlgHom.toRingHom := by
  rw [embeddingProductIsoOfBijective_hom_points, embeddingProductPointEquiv_component]
  exact tensorEmbeddingPointsEquiv_coordinates k K Ω hsplit H R _ τ

variable {H} {H' : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffine H'.X.left] [LocallyOfFiniteType H'.X.hom]

/-- The original homomorphism of H is applied to every point coordinate. -/
theorem embeddingProductPointEquiv_target (f : H ⟶ H')
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) :
    embeddingProductPointEquiv k K Ω hsplit H' R
        (p ≫ ((GroupScheme.baseChange (algebraBaseMap k Ω)).map (map k K f)).hom.hom) =
      embeddingProductPointEquiv k K Ω hsplit H R p ≫
        (embeddingProductMap (Ω := Ω) k f).hom.hom := by
  apply (piPointsEquiv (embeddingFactor k K Ω H')
    ((algSpec (CommRingCat.of Ω)).obj (op R))).injective
  funext τ
  apply (embeddingFactorPointsEquiv k K Ω H' R τ).injective
  rw [embeddingProductPointEquiv_component, piPointsEquiv_embeddingProductMap,
    embeddingFactorPointsEquiv_target, embeddingProductPointEquiv_component,
    baseChangeTensorPointsEquiv_target, tensorEmbeddingPointsEquiv_target]

/-- Naturality for the actual Weil-restriction homomorphism and the product of the actual base changes. -/
theorem embeddingProductIsoOfBijective_naturality (f : H ⟶ H') :
    (GroupScheme.baseChange (algebraBaseMap k Ω)).map (map k K f) ≫
        (embeddingProductIsoOfBijective k K Ω hsplit H').hom =
      (embeddingProductIsoOfBijective k K Ω hsplit H).hom ≫
        embeddingProductMap (Ω := Ω) k f := by
  apply AffinePointComparison.hom_ext (embeddingRestrictionBaseChange k K Ω H)
  intro R p
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [embeddingProductIsoOfBijective_hom_points, embeddingProductIsoOfBijective_hom_points]
  exact embeddingProductPointEquiv_target k K Ω hsplit f R p

end Rings

section Fields

attribute [local instance] coefficientBaseAlgebra coefficientScalarTower

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)
  (H : GroupScheme (Spec (CommRingCat.of K)))
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The actual embedding-product base-change isomorphism for finite-separable affine Weil restriction. -/
def embeddingProductIso :
    (GroupScheme.baseChange (algebraBaseMap k Ω)).obj (groupScheme k K H) ≅
      GroupScheme.pi (fun τ : K →ₐ[k] Ω =>
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H) :=
  embeddingProductIsoOfBijective k K Ω (embeddingEvaluationStatement k K Ω hsplit) H

/-- Each affine-test coordinate is the original tensor-valued point followed by embedding evaluation. -/
theorem embeddingProductIso_coordinate
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    embeddingFactorPointsEquiv k K Ω H R τ
        (piPointsEquiv (embeddingFactor k K Ω H)
          ((algSpec (CommRingCat.of Ω)).obj (op R))
          (p ≫ (embeddingProductIso k K Ω hsplit H).hom.hom.hom) τ) =
      H.affinePointMap (tensorEmbeddingEvaluationMap k K Ω
        (embeddingEvaluationStatement k K Ω hsplit) R τ)
        (baseChangeTensorPointsEquiv k K Ω H R p) :=
  embeddingProductIsoOfBijective_coordinate k K Ω
    (embeddingEvaluationStatement k K Ω hsplit) H R p τ

/-- Exact global-section ring coordinates, with the published tensorEmbeddingEvaluation. -/
theorem embeddingProductIso_coordinates
    (R : CommAlgCat.{u} (CommRingCat.of Ω))
    (p : (embeddingRestrictionBaseChange k K Ω H).affinePoints R) (τ : K →ₐ[k] Ω) :
    (affineSchemePointEquiv K H.X (embeddingCoefficientAlgebra k K Ω R τ)
      (embeddingFactorPointsEquiv k K Ω H R τ
        (piPointsEquiv (embeddingFactor k K Ω H)
          ((algSpec (CommRingCat.of Ω)).obj (op R))
          (p ≫ (embeddingProductIso k K Ω hsplit H).hom.hom.hom) τ))).toAlgHom.toRingHom =
      (tensorEmbeddingEvaluation k K Ω (embeddingEvaluationStatement k K Ω hsplit) R τ).comp
        (affineSchemePointEquiv K H.X (K ⊗[k] R)
          (baseChangeTensorPointsEquiv k K Ω H R p)).toAlgHom.toRingHom :=
  embeddingProductIsoOfBijective_coordinates k K Ω
    (embeddingEvaluationStatement k K Ω hsplit) H R p τ

variable {H} {H' : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffine H'.X.left] [LocallyOfFiniteType H'.X.hom]

/-- The finite-separable field splitting commutes with every actual homomorphism H ⟶ H'. -/
theorem embeddingProductIso_naturality (f : H ⟶ H') :
    (GroupScheme.baseChange (algebraBaseMap k Ω)).map (map k K f) ≫
        (embeddingProductIso k K Ω hsplit H').hom =
      (embeddingProductIso k K Ω hsplit H).hom ≫
        embeddingProductMap (Ω := Ω) k f :=
  embeddingProductIsoOfBijective_naturality k K Ω
    (embeddingEvaluationStatement k K Ω hsplit) f

end Fields

end Langlands.GroupScheme.AffineWeil
