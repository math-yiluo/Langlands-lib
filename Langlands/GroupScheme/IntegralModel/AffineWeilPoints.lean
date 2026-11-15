import Langlands.GroupScheme.IntegralModel.AffineWeilGeneric
import Langlands.GroupScheme.AffineWeilRestrictionTopology
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Integral points of canonical restrictions of integral models -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 3000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

namespace AffineWeil

variable (R : Type u) [CommRing R]
  (X : GroupScheme (Spec (CommRingCat.of R)))

/-- The self-coefficient test and the identity test have the same actual sections. -/
def sectionsCoeffEquiv : rationalPoints X ≃* X.affinePoints (CommAlgCat.of R R) :=
  (X.points.mapIso (ringTestSelfIso R).op).groupIsoToMulEquiv

@[simp] theorem sectionsCoeffEquiv_left (x : rationalPoints X) :
    (sectionsCoeffEquiv R X x).left = x.left := by
  change 𝟙 _ ≫ x.left = x.left
  simp

@[simp] theorem sectionsCoeffEquiv_symm_left (x : X.affinePoints (CommAlgCat.of R R)) :
    ((sectionsCoeffEquiv R X).symm x).left = x.left := by
  change 𝟙 _ ≫ x.left = x.left
  simp

theorem sectionsCoeffEquiv_target
    {Y : GroupScheme (Spec (CommRingCat.of R))} (f : X ⟶ Y) (x : rationalPoints X) :
    sectionsCoeffEquiv R Y (rationalPoints.map f x) =
      sectionsCoeffEquiv R X x ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  simp only [sectionsCoeffEquiv_left, Over.comp_left]
  rfl

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Actual extension of a section is coefficient extension followed by the pullback
comparison, on the existing affine-point carriers. -/
theorem sectionsCoeffEquiv_baseChangeSectionHom (x : rationalPoints X) :
    sectionsCoeffEquiv S ((GroupScheme.baseChange (Spec.algebraMap R S)).obj X)
        (baseChangeSectionHom (Spec.algebraMap R S) X x) =
      affinePointsBaseChangeMulEquiv R S S X
        (X.affinePointMap (CommAlgCat.ofHom (Algebra.ofId R S))
          (sectionsCoeffEquiv R X x)) := by
  apply (affinePointsBaseChangeMulEquiv R S S X).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left, sectionsCoeffEquiv_left,
    baseChangeSectionHom_fst]
  change Spec.algebraMap R S ≫ x.left =
    Spec.map (CommRingCat.ofHom (Algebra.ofId R S).toRingHom) ≫
      (sectionsCoeffEquiv R X x).left
  rw [sectionsCoeffEquiv_left]
  rfl

variable [Module.Finite R S] [Module.Projective R S]
  (Y : GroupScheme (Spec (CommRingCat.of S)))
  [IsAffine Y.X.left] [LocallyOfFiniteType Y.X.hom]

/-- Sections of the actual restriction are precisely sections of the original group. -/
def sectionsEquiv : rationalPoints (groupScheme R S Y) ≃* rationalPoints Y :=
  ((sectionsCoeffEquiv R (groupScheme R S Y)).trans
    (basePointsEquiv R S Y)).trans (sectionsCoeffEquiv S Y).symm

end AffineWeil

namespace IntegralModel.AffineWeilGeneric

variable (A F O K : Type u)
  [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
  [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Algebra A O] [Algebra A K] [Algebra F K]
  [IsScalarTower A O K] [IsScalarTower A F K]
  [Module.Finite A O] [Module.Projective A O]

attribute [local instance] testBaseAlgebra testScalarTower

omit [IsDomain A] [IsFractionRing A F] [IsDomain O] [IsFractionRing O K]
  [Algebra O K] [Algebra A O] [Algebra A K] [Algebra F K]
  [IsScalarTower A O K] [IsScalarTower A F K]
  [Module.Finite A O] [Module.Projective A O] in
def integralTestMap (R : CommAlgCat.{u} (CommRingCat.of F)) :
    CommAlgCat.of A A ⟶ CommAlgCat.of A R :=
  CommAlgCat.ofHom (Algebra.ofId A R)

omit [IsDomain A] [IsFractionRing A F] [IsDomain O] [IsFractionRing O K]
  [Algebra O K] [Algebra A O] [Algebra A K] [Algebra F K]
  [IsScalarTower A O K] [IsScalarTower A F K]
  [Module.Finite A O] [Module.Projective A O] in
theorem sectionsCoeffEquiv_baseChangeSelf
    (X : GroupScheme (Spec (CommRingCat.of A))) (x : rationalPoints X) :
    AffineWeil.sectionsCoeffEquiv F ((GroupScheme.baseChange (Spec.algebraMap A F)).obj X)
        (baseChangeSectionHom (Spec.algebraMap A F) X x) =
      affinePointsBaseChangeMulEquiv A F (CommAlgCat.of F F) X
        (X.affinePointMap (integralTestMap A F (CommAlgCat.of F F))
          (AffineWeil.sectionsCoeffEquiv A X x)) := by
  apply (affinePointsBaseChangeMulEquiv A F (CommAlgCat.of F F) X).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left,
    AffineWeil.sectionsCoeffEquiv_left, baseChangeSectionHom_fst]
  change Spec.algebraMap A F ≫ x.left =
    Spec.map (CommRingCat.ofHom _) ≫ (AffineWeil.sectionsCoeffEquiv A X x).left
  rw [AffineWeil.sectionsCoeffEquiv_left]
  rfl

omit [Module.Projective A O] in
theorem coefficientEquiv_integral (R : CommAlgCat.{u} (CommRingCat.of F))
    (b : K ⊗[F] R →ₐ[K] K) :
    ((b.restrictScalars O).comp (coefficientEquiv A F O K R).toAlgHom).comp
        (Algebra.TensorProduct.lTensor (S := O) O (Algebra.ofId A R)) =
      (Algebra.ofId O K).comp (Algebra.TensorProduct.rid A O O).toAlgHom := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul o a =>
    change b (coefficientEquiv A F O K R (o ⊗ₜ[A] algebraMap A R a)) =
      algebraMap O K (a • o)
    rw [coefficientEquiv_tmul]
    rw [IsScalarTower.algebraMap_apply A F R,
      Algebra.algebraMap_eq_smul_one (algebraMap A F a),
      ← TensorProduct.smul_tmul]
    change b (algebraMap K (K ⊗[F] R)
      ((algebraMap A F a) • algebraMap O K o)) = _
    rw [b.commutes]
    simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← IsScalarTower.algebraMap_apply A F K,
      IsScalarTower.algebraMap_apply A O K, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel O K G)

local instance : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

omit [IsDomain A] [IsFractionRing A F] [Algebra A K] [Algebra F K]
  [IsScalarTower A O K] [IsScalarTower A F K] in
theorem integralTensorPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of F))
    (p : (AffineWeil.groupScheme A O M.group).affinePoints (CommAlgCat.of A A)) :
    AffineWeil.pointsEquiv A O M.group R
        ((AffineWeil.groupScheme A O M.group).affinePointMap (integralTestMap A F R) p) =
      M.group.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := O) O (integralTestMap A F R).hom))
        (AffineWeil.pointsEquiv A O M.group A p) :=
  AffineWeil.pointsEquiv_naturality A O M.group (integralTestMap A F R).hom p

omit [Module.Projective A O] in
theorem coefficientPoints_integral (R : CommAlgCat.{u} (CommRingCat.of F))
    (b : K ⊗[F] R →ₐ[K] K)
    (p : M.group.affinePoints (CommAlgCat.of O (O ⊗[A] A))) :
    M.group.affinePointMap (CommAlgCat.ofHom
        ((b.restrictScalars O).comp (coefficientEquiv A F O K R).toAlgHom))
      (M.group.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := O) O (integralTestMap A F R).hom)) p) =
      M.group.affinePointMap (CommAlgCat.ofHom (Algebra.ofId O K))
        (AffineWeil.tensorUnitPointsEquiv A O M.group p) := by
  change ((M.group.affinePointMap _).comp (M.group.affinePointMap _)) p = _
  rw [← affinePointMap_comp]
  have hc :
      CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := O) O
          (integralTestMap A F R).hom) ≫
        CommAlgCat.ofHom
          ((b.restrictScalars O).comp (coefficientEquiv A F O K R).toAlgHom) =
      CommAlgCat.ofHom (Algebra.TensorProduct.rid A O O).toAlgHom ≫
        CommAlgCat.ofHom (Algebra.ofId O K) := by
    apply CommAlgCat.hom_ext
    exact coefficientEquiv_integral A F O K R b
  rw [hc, affinePointMap_comp]
  rfl

omit [Module.Projective A O] in
theorem genericTensorPointsEquiv_coefficient
    (R : CommAlgCat.{u} (CommRingCat.of F)) (b : K ⊗[F] R →ₐ[K] K)
    (p : M.group.affinePoints (CommAlgCat.of O (O ⊗[A] R))) :
    G.affinePointMap (CommAlgCat.ofHom b)
        (genericTensorPointsEquiv A F O K M R p) =
      affinePointsBaseChangeMulEquiv O K K M.group
        (M.group.affinePointMap (CommAlgCat.ofHom
          ((b.restrictScalars O).comp
            (coefficientEquiv A F O K R).toAlgHom)) p) ≫
        M.genericIso.hom.hom.hom := by
  change G.affinePointMap (CommAlgCat.ofHom b)
    (affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) M.group
      (M.group.affinePointMap
        (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom) p) ≫
      M.genericIso.hom.hom.hom) = _
  have ht :
      G.affinePointMap (CommAlgCat.ofHom b)
        (affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) M.group
          (M.group.affinePointMap
            (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom) p) ≫
          M.genericIso.hom.hom.hom) =
      M.genericFibre.affinePointMap
        (CommAlgCat.ofHom b)
        (affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) M.group
          (M.group.affinePointMap
            (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom) p)) ≫
        M.genericIso.hom.hom.hom := by
    simp only [affinePointMap_apply, Category.assoc]
  rw [ht, affinePointsBaseChangeMulEquiv_naturality]
  congr 2
  change ((M.group.affinePointMap _).comp (M.group.affinePointMap _)) p = _
  rw [← affinePointMap_comp]
  rfl

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The canonical generic restriction has the original generic rational points. -/
def genericSectionsEquiv :
    rationalPoints (genericGroup A F O K G) ≃* rationalPoints G := by
  letI := genericFinite A F O K
  exact AffineWeil.sectionsEquiv F K G

variable [Smooth M.group.X.hom]

/-- Sections of the canonical restricted model are exactly sections of the original model. -/
def modelSectionsEquiv : (model A F O K M).integralSections ≃* M.integralSections :=
  AffineWeil.sectionsEquiv A O M.group

theorem model_integralPointMap (x : (model A F O K M).integralSections) :
    genericSectionsEquiv A F O K (G := G) ((model A F O K M).integralPointMap x) =
      M.integralPointMap (modelSectionsEquiv A F O K M x) := by
  let := genericFinite A F O K
  apply (AffineWeil.sectionsCoeffEquiv K G).injective
  change
    AffineWeil.basePointsEquiv F K G
      (AffineWeil.sectionsCoeffEquiv F (genericGroup A F O K G)
        (rationalPoints.map (iso A F O K M).hom
          (baseChangeSectionHom (Spec.algebraMap A F)
            (AffineWeil.groupScheme A O M.group) x))) = _
  rw [AffineWeil.sectionsCoeffEquiv_target, iso_hom_points]
  change AffineWeil.tensorUnitPointsEquiv F K G
    (AffineWeil.pointsEquiv F K G (CommAlgCat.of F F)
      (pointEquiv A F O K M (CommAlgCat.of F F)
        (AffineWeil.sectionsCoeffEquiv F _
          (baseChangeSectionHom (Spec.algebraMap A F)
            (AffineWeil.groupScheme A O M.group) x)))) = _
  dsimp only [pointEquiv, MulEquiv.trans_apply]
  rw [MulEquiv.apply_symm_apply, sectionsCoeffEquiv_baseChangeSelf]
  dsimp only [AffineWeil.baseChangeTensorPointsEquiv, MulEquiv.trans_apply]
  erw [MulEquiv.symm_apply_apply]
  rw [integralTensorPointsEquiv A F O K M (CommAlgCat.of F F)]
  rw [AffineWeil.tensorUnitPointsEquiv_apply]
  rw [genericTensorPointsEquiv_coefficient A F O K M (CommAlgCat.of F F)
    (Algebra.TensorProduct.rid F K K).toAlgHom]
  rw [coefficientPoints_integral A F O K M (CommAlgCat.of F F)
    (Algebra.TensorProduct.rid F K K).toAlgHom]
  change affinePointsBaseChangeMulEquiv O K K M.group
      (M.group.affinePointMap (CommAlgCat.ofHom (Algebra.ofId O K))
        (AffineWeil.sectionsCoeffEquiv O M.group (modelSectionsEquiv A F O K M x))) ≫
      M.genericIso.hom.hom.hom = _
  rw [← AffineWeil.sectionsCoeffEquiv_baseChangeSectionHom]
  rw [← AffineWeil.sectionsCoeffEquiv_target]
  rfl

/-- The canonical restriction identifies the actual integral-point subgroups. -/
theorem model_mem_integralPoints (g : rationalPoints (genericGroup A F O K G)) :
    g ∈ (model A F O K M).integralPoints ↔
      genericSectionsEquiv A F O K (G := G) g ∈ M.integralPoints := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨modelSectionsEquiv A F O K M x, (model_integralPointMap A F O K M x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(modelSectionsEquiv A F O K M).symm x, ?_⟩
    apply (genericSectionsEquiv A F O K (G := G)).injective
    rw [model_integralPointMap, MulEquiv.apply_symm_apply, hx]

theorem model_integralPoints_comap :
    (model A F O K M).integralPoints =
      M.integralPoints.comap (genericSectionsEquiv A F O K (G := G)).toMonoidHom := by
  ext g
  exact model_mem_integralPoints A F O K M g

theorem model_integralPoints_map :
    (model A F O K M).integralPoints.map
        (genericSectionsEquiv A F O K (G := G)).toMonoidHom =
      M.integralPoints := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (model_mem_integralPoints A F O K M h).mp hh
  · intro hg
    refine ⟨(genericSectionsEquiv A F O K (G := G)).symm g, ?_,
      MulEquiv.apply_symm_apply _ g⟩
    apply (model_mem_integralPoints A F O K M
      ((genericSectionsEquiv A F O K (G := G)).symm g)).mpr
    rw [MulEquiv.apply_symm_apply]
    exact hg

end IntegralModel.AffineWeilGeneric

end Langlands.GroupScheme
