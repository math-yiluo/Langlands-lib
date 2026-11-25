/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import all WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
import all WeilConjectures.AlgebraicGeometry.SfGraphFirstProjectionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence

/-! # Canonical normalization of identity projection

(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem exact_comparison_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Functor.rightDerivedFunctorNatIso e).hom ≫
        G.rightDerivedFunctorIsoMapDerivedCategory.hom =
      F.rightDerivedFunctorIsoMapDerivedCategory.hom ≫
        (Functor.mapDerivedCategoryNatIso e).hom := by
  apply F.rightDerivedFunctor.rightDerived_ext F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  ext K
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app]

private theorem transport_identity_projection
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C) {F R : C ⥤ C}
    (c : F ≅ R) (d : R ≅ 𝟭 C) (V M N : C) (ψ : N ⟶ M)
    (p : (T.obj (F.obj V)).obj M ⟶ F.obj ((T.obj V).obj N))
    (q : (T.obj (R.obj V)).obj M ⟶ R.obj ((T.obj V).obj N))
    (hp : p ≫ c.hom.app ((T.obj V).obj N) = (T.map (c.hom.app V)).app M ≫ q)
    (hq : (T.map (d.inv.app V)).app M ≫ q ≫ R.map ((T.obj V).map ψ) =
      d.inv.app ((T.obj V).obj M)) :
    (T.map ((c ≪≫ d).inv.app V)).app M ≫ p ≫ F.map ((T.obj V).map ψ) =
      (c ≪≫ d).inv.app ((T.obj V).obj M) := by
  have ht : (T.map (c.inv.app V)).app M ≫ (T.map (c.hom.app V)).app M = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, NatTrans.id_app]
  apply (cancel_mono (c.hom.app ((T.obj V).obj M))).mp
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [c.hom.naturality ((T.obj V).map ψ), reassoc_of% hp, reassoc_of% ht]
  simpa only [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id] using hq

namespace AlgebraicGeometry.Etale.SupportedTrace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

attribute [local instance] Sheaf.monoidalCategory

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local irreducible] derivedTensor upperStar lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  leftDerivedUpperStarId
  DerivedCategory instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  leftDerivedUpperStarTensorComparison derivedUpperStarLowerStarAdjunction

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The projection map for the identity, normalized by the specified direct-image identity.
Source: Stacks Project, Tags 0B56 and 0DV0; identity projection normalization in
WeilConjectures.AlgebraicGeometry.SfGraphFirstProjectionSquare and the proper coincidence square in
WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence
(auxiliary; not a blueprint node).

Proof: use identity_pullback_tensor to identify the pullback tensor comparison with the
canonical identity pullback isomorphism. Transpose the ordinary direct-image projection
through the derived pullback/direct-image adjunction. Its defining transpose is tensor
comparison followed by the counit tensor identity. Substituting the preceding identity
and the identity counit equation gives normalized_identity_projection; the conjugate
right comparison is rightDerivedLowerStarIdIso by derived_identity_conjugate. Thus the
ordinary projection, followed by the tensor of the identity pullback comparison, becomes
the identity under these pullback and direct-image comparisons. Transport this equation
through projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar. The composite
of proper coincidence with rightDerivedLowerStarIdIso is exactly
rightDerivedLowerShriekIdIsoOfLowerStar: naturality of the right-derived/exact-functor
comparison identifies the two displayed constructions. Naturality moves the proper
comparison across the tensor map. Cancel its inverse and then the direct-image identity
comparison to obtain the inverse-oriented equality below. No section or composition of
two nonidentity scheme maps occurs in this normalization. -/
theorem identityProjectionNormalization (X : Scheme.{u})
    (V M : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).inv.app V)).app M ≫
      (projectionIso A (𝟙 X) V).hom.app M ≫
      (push A (𝟙 X)).map (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app M)) =
      (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).inv.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj M) := by
  have he (P Q : DerivedCategoryModule A X) :
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj P).obj Q) =
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) (𝟙 X)).app P).app Q ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).map
            ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app P)).app
              ((upperStar (ModuleCat.{u + 1} A) (𝟙 X)).leftDerivedFunctor.obj Q) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj P).map
            ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app Q) := by
    have h := identity_pullback_tensor A X P Q
    rw [MonoidalCategory.tensorHom_def] at h
    symm
    dsimp at h ⊢
    simpa only [leftDerivedUpperStarTensorIso_hom, derivedTensor,
      MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.curriedTensor_map_app,
      MonoidalCategory.curriedTensor_obj_map, Functor.id_obj, Functor.comp_obj,
      Category.assoc] using h
  have hn := normalized_identity_projection
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
    (derivedTensor (ModuleCat.{u + 1} A) X)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) (𝟙 X))
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X) he V M
  rw [derived_identity_conjugate] at hn
  change ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((rightDerivedLowerStarIdIso A X).inv.app V)).app M ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app V).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctor.map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app M)) =
      (rightDerivedLowerStarIdIso A X).inv.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj M) at hn
  have hd : rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X =
      rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 X) ≪≫
        rightDerivedLowerStarIdIso A X := by
    apply Iso.ext
    have h := exact_comparison_naturality (lowerStarId (ModuleCat.{u + 1} A) X)
    simpa only [rightDerivedLowerShriekIdIsoOfLowerStar, rightDerivedLowerStarIdIso,
      Iso.trans_hom, Category.assoc] using
      congrArg (fun t ↦
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 X)).hom ≫
          t ≫ (Functor.mapDerivedCategoryIdIso _).hom) h
  have hc := projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) (𝟙 X) V M
  have hproj : (projectionIso A (𝟙 X) V).hom =
      (projectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app V := by
    rfl
  rw [hd, hproj]
  exact transport_identity_projection (derivedTensor (ModuleCat.{u + 1} A) X)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 X))
    (rightDerivedLowerStarIdIso A X) V M _
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app M)
    (((projectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app V).app M)
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app V).app M)
    hc hn

end AlgebraicGeometry.Etale.SupportedTrace
