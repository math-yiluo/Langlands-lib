import Langlands.GroupScheme.IntegralModel.AffineWeil
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Finiteness

/-! # Generic fibres of restrictions of actual integral models -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 3000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct nonZeroDivisors

namespace Langlands.GroupScheme.IntegralModel.AffineWeilGeneric

variable (A F O K : Type u)
  [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
  [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Algebra A O] [Algebra A K] [Algebra F K]
  [IsScalarTower A O K] [IsScalarTower A F K]
  [Module.Finite A O] [Module.Projective A O]

omit [IsDomain A] [IsDomain O] [IsFractionRing O K]
  [Module.Finite A O] [Module.Projective A O] in
include F K in
theorem coefficientFaithful : FaithfulSMul A O := by
  apply (faithfulSMul_iff_algebraMap_injective A O).mpr
  have hi : Function.Injective ((algebraMap O K).comp (algebraMap A O)) := by
    rw [← IsScalarTower.algebraMap_eq A O K, IsScalarTower.algebraMap_eq A F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective A F)
  exact Function.Injective.of_comp hi

omit [Module.Projective A O] in
include A O in
theorem genericFinite : Module.Finite F K := by
  let := coefficientFaithful A F O K
  exact Module.Finite.of_isLocalization A O A⁰

local instance testBaseAlgebra (R : CommAlgCat.{u} (CommRingCat.of F)) :
    Algebra A R := Algebra.compHom R (algebraMap A F)

local instance testScalarTower (R : CommAlgCat.{u} (CommRingCat.of F)) :
    IsScalarTower A F R := IsScalarTower.of_algebraMap_eq' rfl

/-- The original tensor coefficients agree after passing from the integral
coefficient ring to its fraction field. -/
def coefficientEquiv (R : CommAlgCat.{u} (CommRingCat.of F)) :
    O ⊗[A] R ≃ₐ[O] K ⊗[F] R := by
  let := coefficientFaithful A F O K
  exact (Algebra.IsPushout.cancelBaseChangeAlg A O F K R).symm

omit [Module.Projective A O] in
@[simp] theorem coefficientEquiv_tmul
    (R : CommAlgCat.{u} (CommRingCat.of F)) (o : O) (r : R) :
    coefficientEquiv A F O K R (o ⊗ₜ[A] r) = algebraMap O K o ⊗ₜ[F] r := by
  let := coefficientFaithful A F O K
  exact Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul A O F K R o r

omit [Module.Projective A O] in
theorem coefficientEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of F)} (a : R ⟶ R') :
    (coefficientEquiv A F O K R').toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := O) O (a.hom.restrictScalars A)) =
      ((Algebra.TensorProduct.lTensor (S := K) K a.hom).restrictScalars O).comp
        (coefficientEquiv A F O K R).toAlgHom := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul o r => simp
  | add x y hx hy => simp_all

/-- Actual restriction of the generic group; generic finiteness follows from the
finite integral coefficient algebra, rather than being an additional input. -/
abbrev genericGroup (G : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    GroupScheme (Spec (CommRingCat.of F)) := by
  letI := genericFinite A F O K
  exact AffineWeil.groupScheme F K G

instance genericGroup_isAffine (G : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    IsAffine (genericGroup A F O K G).X.left := by
  dsimp only [genericGroup]
  infer_instance

/-- Actual restriction of a homomorphism between generic groups. -/
abbrev genericMap {G H : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] (f : G ⟶ H) :
    genericGroup A F O K G ⟶ genericGroup A F O K H := by
  letI := genericFinite A F O K
  exact AffineWeil.map F K f

variable {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel O K G)

local instance : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- The original generic identification on actual tensor-valued affine points. -/
def genericTensorPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of F)) :
    M.group.affinePoints (CommAlgCat.of O (O ⊗[A] R)) ≃*
      G.affinePoints (CommAlgCat.of K (K ⊗[F] R)) :=
  ((M.group.affinePointFunctor.mapIso
      (CommAlgCat.isoMk (coefficientEquiv A F O K R))).groupIsoToMulEquiv.trans
    (affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) M.group)).trans
      (((yonedaGrp.mapIso M.genericIso).app
        (op ((algSpec (CommRingCat.of K)).obj
          (op (CommAlgCat.of K (K ⊗[F] R)))))).groupIsoToMulEquiv)

omit [Module.Projective A O] in
theorem coefficientPoints_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of F)} (a : R ⟶ R')
    (p : M.group.affinePoints (CommAlgCat.of O (O ⊗[A] R))) :
    M.group.affinePointMap (CommAlgCat.ofHom (coefficientEquiv A F O K R').toAlgHom)
        (M.group.affinePointMap (CommAlgCat.ofHom
          (Algebra.TensorProduct.lTensor (S := O) O (a.hom.restrictScalars A))) p) =
      M.group.affinePointMap (CommAlgCat.ofHom
          ((Algebra.TensorProduct.lTensor (S := K) K a.hom).restrictScalars O))
        (M.group.affinePointMap
          (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom) p) := by
  have hc :
      CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := O) O
          (a.hom.restrictScalars A)) ≫
        CommAlgCat.ofHom (coefficientEquiv A F O K R').toAlgHom =
      CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom ≫
        CommAlgCat.ofHom
          ((Algebra.TensorProduct.lTensor (S := K) K a.hom).restrictScalars O) := by
    apply CommAlgCat.hom_ext
    exact coefficientEquiv_naturality A F O K a
  change ((M.group.affinePointMap _).comp (M.group.affinePointMap _)) p =
    ((M.group.affinePointMap _).comp (M.group.affinePointMap _)) p
  rw [← affinePointMap_comp, ← affinePointMap_comp, hc]

omit [Module.Projective A O] in
theorem genericTensorPointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of F)} (a : R ⟶ R')
    (p : M.group.affinePoints (CommAlgCat.of O (O ⊗[A] R))) :
    genericTensorPointsEquiv A F O K M R'
        (M.group.affinePointMap (CommAlgCat.ofHom
          (Algebra.TensorProduct.lTensor (S := O) O (a.hom.restrictScalars A))) p) =
      G.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := K) K a.hom))
          (genericTensorPointsEquiv A F O K M R p) := by
  change
    affinePointsBaseChangeMulEquiv O K (K ⊗[F] R') M.group
        (M.group.affinePointMap
          (CommAlgCat.ofHom (coefficientEquiv A F O K R').toAlgHom)
          (M.group.affinePointMap (CommAlgCat.ofHom
            (Algebra.TensorProduct.lTensor (S := O) O (a.hom.restrictScalars A))) p)) ≫
          M.genericIso.hom.hom.hom =
      G.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := K) K a.hom))
        (affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) M.group
          (M.group.affinePointMap
            (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom) p) ≫
          M.genericIso.hom.hom.hom)
  rw [coefficientPoints_naturality, ← affinePointsBaseChangeMulEquiv_naturality]
  simp only [affinePointMap_apply, Category.assoc]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Actual affine points of the restricted model's generic fibre are those of
restriction of the original generic group. -/
def pointEquiv (R : CommAlgCat.{u} (CommRingCat.of F)) :
    (AffineWeil.BaseChange.source A O F M.group).affinePoints R ≃*
      (genericGroup A F O K G).affinePoints R := by
  letI := genericFinite A F O K
  exact ((AffineWeil.baseChangeTensorPointsEquiv A O F M.group R).trans
    (genericTensorPointsEquiv A F O K M R)).trans (AffineWeil.pointsEquiv F K G R).symm

theorem pointEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of F)} (a : R ⟶ R')
    (p : (AffineWeil.BaseChange.source A O F M.group).affinePoints R) :
    pointEquiv A F O K M R'
        ((AffineWeil.BaseChange.source A O F M.group).affinePointMap a p) =
      (genericGroup A F O K G).affinePointMap a (pointEquiv A F O K M R p) := by
  let := genericFinite A F O K
  apply (AffineWeil.pointsEquiv F K G R').injective
  have hn := AffineWeil.pointsEquiv_naturality F K G a.hom
    (pointEquiv A F O K M R p)
  dsimp only [pointEquiv, MulEquiv.trans_apply] at hn ⊢
  simp only [MulEquiv.apply_symm_apply] at hn ⊢
  rw [AffineWeil.baseChangeTensorPointsEquiv_naturality,
    genericTensorPointsEquiv_naturality]
  exact ((AffineWeil.pointsEquiv F K G R').apply_symm_apply _).trans hn.symm

/-- The actual group-valued affine-point functors agree naturally. -/
def affinePointIso :
    (AffineWeil.BaseChange.source A O F M.group).affinePointFunctor ≅
      (genericGroup A F O K G).affinePointFunctor :=
  NatIso.ofComponents (fun R => (pointEquiv A F O K M R).toGrpIso) (by
    intro R R' a
    ext p
    exact pointEquiv_naturality A F O K M a p)

/-- The canonical actual generic-fibre isomorphism for the restricted model. -/
def iso :
    AffineWeil.BaseChange.source A O F M.group ≅ genericGroup A F O K G :=
  AffinePointComparison.iso (affinePointIso A F O K M)

theorem iso_hom_points (R : CommAlgCat.{u} (CommRingCat.of F))
    (p : (AffineWeil.BaseChange.source A O F M.group).affinePoints R) :
    p ≫ (iso A F O K M).hom.hom.hom = pointEquiv A F O K M R p :=
  AffinePointComparison.iso_hom_points (affinePointIso A F O K M) R p

variable {H : GroupScheme (Spec (CommRingCat.of K))}
  (N : IntegralModel O K H) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  {f : G ⟶ H} (φ : M.Hom N f)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
private theorem baseChangePoints_target (R : CommAlgCat.{u} (CommRingCat.of F))
    (p : M.group.affinePoints (CommAlgCat.of O (K ⊗[F] R))) :
    affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) N.group (p ≫ φ.hom.hom.hom) =
      affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) M.group p ≫
        ((GroupScheme.baseChange (Spec.algebraMap O K)).map φ.hom).hom.hom := by
  apply (affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) N.group).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left]
  change (p ≫ φ.hom.hom.hom).left =
    ((affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) M.group p).left ≫
      ((Over.pullback (Spec.algebraMap O K)).map φ.hom.hom.hom).left) ≫
        CategoryTheory.Limits.pullback.fst N.group.X.hom (Spec.algebraMap O K)
  simp only [Over.pullback_map_left, Category.assoc,
    CategoryTheory.Limits.pullback.lift_fst]
  rw [← Category.assoc, affinePointsBaseChangeMulEquiv_eq_ringPoint,
    Langlands.AlgebraicGeometry.PointTopology.ringPointBaseChangeEquiv_left_fst]
  rfl

omit [Module.Projective A O] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
theorem genericTensorPointsEquiv_target (R : CommAlgCat.{u} (CommRingCat.of F))
    (p : M.group.affinePoints (CommAlgCat.of O (O ⊗[A] R))) :
    genericTensorPointsEquiv A F O K N R (p ≫ φ.hom.hom.hom) =
      genericTensorPointsEquiv A F O K M R p ≫ f.hom.hom := by
  change
    affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) N.group
        (N.group.affinePointMap
          (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom)
          (p ≫ φ.hom.hom.hom)) ≫ N.genericIso.hom.hom.hom =
      (affinePointsBaseChangeMulEquiv O K (K ⊗[F] R) M.group
        (M.group.affinePointMap
          (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom) p) ≫
        M.genericIso.hom.hom.hom) ≫ f.hom.hom
  have hc : N.group.affinePointMap
      (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom)
        (p ≫ φ.hom.hom.hom) =
      M.group.affinePointMap
        (CommAlgCat.ofHom (coefficientEquiv A F O K R).toAlgHom) p ≫
          φ.hom.hom.hom := by
    simp only [affinePointMap_apply, Category.assoc]
  rw [hc, baseChangePoints_target F O K M N φ, Category.assoc]
  change _ ≫
      (((GroupScheme.baseChange (Spec.algebraMap O K)).map φ.hom ≫
        N.genericIso.hom).hom.hom) = _
  rw [φ.generic_comm]
  rfl

theorem pointEquiv_target (R : CommAlgCat.{u} (CommRingCat.of F))
    (p : (AffineWeil.BaseChange.source A O F M.group).affinePoints R) :
    pointEquiv A F O K N R
        (p ≫ (AffineWeil.BaseChange.sourceMap A O F M.group φ.hom).hom.hom) =
      pointEquiv A F O K M R p ≫ (genericMap A F O K f).hom.hom := by
  let := genericFinite A F O K
  apply (AffineWeil.pointsEquiv F K H R).injective
  have ht := AffineWeil.map_affinePoints F K f R (pointEquiv A F O K M R p)
  dsimp only [pointEquiv, MulEquiv.trans_apply] at ht ⊢
  simp only [MulEquiv.apply_symm_apply] at ht ⊢
  rw [AffineWeil.BaseChange.sourcePointsEquiv_target,
    genericTensorPointsEquiv_target A F O K M N φ]
  exact ((AffineWeil.pointsEquiv F K H R).apply_symm_apply _).trans ht.symm

/-- The canonical generic identification commutes with every compatible
integral-model homomorphism, without a new generic-square premise. -/
theorem iso_naturality :
    AffineWeil.BaseChange.sourceMap A O F M.group φ.hom ≫ (iso A F O K N).hom =
      (iso A F O K M).hom ≫ genericMap A F O K f := by
  apply AffinePointComparison.hom_ext (AffineWeil.BaseChange.source A O F M.group)
  intro R p
  change
    (p ≫ (AffineWeil.BaseChange.sourceMap A O F M.group φ.hom).hom.hom) ≫
        (iso A F O K N).hom.hom.hom =
      (p ≫ (iso A F O K M).hom.hom.hom) ≫ (genericMap A F O K f).hom.hom
  rw [iso_hom_points, iso_hom_points]
  exact pointEquiv_target A F O K M N φ R p

variable [Smooth M.group.X.hom]

/-- Actual restriction of a smooth integral model, with its canonical generic
identification with restriction of the original generic group. -/
def model : IntegralModel A F (genericGroup A F O K G) :=
  IntegralModel.affineWeil A F O M.group (iso A F O K M)

theorem model_isSmooth : (model A F O K M).IsSmooth :=
  IntegralModel.affineWeil_isSmooth A F O M.group (iso A F O K M)

variable [Smooth N.group.X.hom]

/-- Actual restriction of an original compatible integral-model homomorphism. -/
def modelHom :
    (model A F O K M).Hom (model A F O K N) (genericMap A F O K f) :=
  IntegralModel.affineWeilHom A F O (iso A F O K M) (iso A F O K N) φ.hom
    (iso_naturality A F O K M N φ)

theorem model_hom_eq
    (ψ : (model A F O K M).Hom (model A F O K N) (genericMap A F O K f)) :
    ψ.hom = AffineWeil.map A O φ.hom :=
  ψ.hom_eq (modelHom A F O K M N φ)

variable [IsLocalRing A]

theorem model_specialFibreMap_eq
    (ψ : (model A F O K M).Hom (model A F O K N) (genericMap A F O K f)) :
    ψ.specialFibreMap =
      AffineWeil.BaseChange.sourceMap A O (IsLocalRing.ResidueField A) M.group φ.hom :=
  IntegralModel.affineWeil_specialFibreMap_eq A F O (iso A F O K M)
    (iso A F O K N) φ.hom (iso_naturality A F O K M N φ) ψ

end Langlands.GroupScheme.IntegralModel.AffineWeilGeneric
