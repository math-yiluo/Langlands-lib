/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPullComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralExchangeTargetAdjunct

/-! # Flat coefficient extension and ambient exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.RationalP1

local instance instEssentiallySmallProfinite_flatCoefficientPullbackCube
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedPullIso derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.leftDerivedUpperStarComp condensedAmbientPullbackComparison
  Adjunction.pullIsoOfComapIso Adjunction.pushHomOfComapIso

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward Mod.regular

private theorem replace_iso_rectangle
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {P Q R S : D}
    (θ θ' : A ≅ B) (κ κ' : R ≅ S)
    (a : F.obj A ≅ P) (b : P ≅ R) (c : F.obj B ≅ Q) (d : Q ≅ S)
    (hθ : θ = θ') (hκ : κ = κ')
    (h : F.mapIso θ' ≪≫ c ≪≫ d = a ≪≫ b ≪≫ κ') :
    F.mapIso θ ≪≫ c ≪≫ d = a ≪≫ b ≪≫ κ := by
  rw [hθ, hκ]
  exact h

private theorem pullback_square_of_iso
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
    {U : C₁ ⥤ C₂} {V : C₃ ⥤ C₄} {Ue : D₁ ⥤ D₂} {Ve : D₃ ⥤ D₄}
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    (θ : G ⋙ V ≅ U ⋙ H) (θe : Ge ⋙ Ve ≅ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ≅ T₂ ⋙ He) (M : C₁)
    (h : T₄.mapIso (θ.app M) ≪≫ αH.app (U.obj M) ≪≫ He.mapIso (αU.app M) =
      αV.app (G.obj M) ≪≫ Ve.mapIso (αG.app M) ≪≫ θe.app (T₁.obj M)) :
    Adjunction.coefficientPullbackSquare θ.hom θe.hom αU αV αG.hom αH.hom M := by
  simpa only [Adjunction.coefficientPullbackSquare, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc] using congrArg Iso.hom h

private theorem native_pull_comp
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory (Modules Λ Z)) :
    (derivedScalars a X).mapIso ((CondensedRing.leftDerivedUpperStarComp Λ f g).app K) ≪≫
        (derivedPullIso a f).app ((moduleObjectDerivedPullback Λ g).obj K) ≪≫
        (moduleObjectDerivedPullback Λ' f).mapIso ((derivedPullIso a g).app K) =
      (derivedPullIso a (f ≫ g)).app K ≪≫
        (CondensedRing.leftDerivedUpperStarComp Λ' f g).app ((derivedScalars a Z).obj K) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Iso.app_hom, Functor.mapIso_hom] using
      congr_app (derived_pull_comp a f g) K

private theorem native_pull_eq
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X Y : Scheme.{u}} (f g : X ⟶ Y) (w : f = g)
    (K : DerivedCategory (Modules Λ Y)) :
    (derivedScalars a X).mapIso
        ((eqToIso (congrArg (fun h : X ⟶ Y ↦
          (CondensedRing.upperStar Λ h).leftDerivedFunctor) w)).app K) ≪≫
        (derivedPullIso a g).app K =
      (derivedPullIso a f).app K ≪≫
        (eqToIso (congrArg (fun h : X ⟶ Y ↦
          (CondensedRing.upperStar Λ' h).leftDerivedFunctor) w)).app
          ((derivedScalars a Y).obj K) := by
  subst g
  change (derivedScalars a X).mapIso (Iso.refl _) ≪≫ (derivedPullIso a f).app K =
    (derivedPullIso a f).app K ≪≫ Iso.refl _
  rw [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]

private theorem triple_iso_app
    {C D : Type*} [Category C] [Category D] {F G H I : C ⥤ D}
    (p : G ≅ F) (q : G ≅ H) (r : H ≅ I) (K : C) :
    (p.symm ≪≫ q ≪≫ r).app K = (p.app K).symm ≪≫ q.app K ≪≫ r.app K := by
  rfl

private theorem comparison_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : ChosenCartesianSquare g' f' f g) (K : DerivedCategory (Modules Λ Y)) :
    (condensedAmbientPullbackComparison Λ sq).app K =
      ((CondensedRing.leftDerivedUpperStarComp Λ f' g).app K).symm ≪≫
        (eqToIso (congrArg (fun h : X' ⟶ Y ↦
          (CondensedRing.upperStar Λ h).leftDerivedFunctor) sq.toCommSq.w.symm)).app K ≪≫
        (CondensedRing.leftDerivedUpperStarComp Λ g' f).app K := by
  unfold condensedAmbientPullbackComparison
  exact triple_iso_app _ _ _ K

private theorem native_pull_cube_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : ChosenCartesianSquare g' f' f g) (K : DerivedCategory (Modules Λ Y)) :
    (derivedScalars a X').mapIso ((condensedAmbientPullbackComparison Λ sq).app K) ≪≫
        (derivedPullIso a g').app ((moduleObjectDerivedPullback Λ f).obj K) ≪≫
        (moduleObjectDerivedPullback Λ' g').mapIso ((derivedPullIso a f).app K) =
      (derivedPullIso a f').app ((moduleObjectDerivedPullback Λ g).obj K) ≪≫
        (moduleObjectDerivedPullback Λ' f').mapIso ((derivedPullIso a g).app K) ≪≫
        (condensedAmbientPullbackComparison Λ' sq).app ((derivedScalars a Y).obj K) := by
  have h := mapped_iso_rectangle (derivedScalars a X')
    ((CondensedRing.leftDerivedUpperStarComp Λ f' g).app K)
    ((CondensedRing.leftDerivedUpperStarComp Λ g' f).app K)
    ((eqToIso (congrArg (fun h : X' ⟶ Y ↦ (CondensedRing.upperStar Λ h).leftDerivedFunctor)
      sq.toCommSq.w.symm)).app K)
    ((CondensedRing.leftDerivedUpperStarComp Λ' f' g).app ((derivedScalars a Y).obj K))
    ((CondensedRing.leftDerivedUpperStarComp Λ' g' f).app ((derivedScalars a Y).obj K))
    ((eqToIso (congrArg (fun h : X' ⟶ Y ↦ (CondensedRing.upperStar Λ' h).leftDerivedFunctor)
      sq.toCommSq.w.symm)).app
      ((derivedScalars a Y).obj K))
    ((derivedPullIso a f').app ((moduleObjectDerivedPullback Λ g).obj K))
    ((moduleObjectDerivedPullback Λ' f').mapIso ((derivedPullIso a g).app K))
    ((derivedPullIso a g').app ((moduleObjectDerivedPullback Λ f).obj K))
    ((moduleObjectDerivedPullback Λ' g').mapIso ((derivedPullIso a f).app K))
    ((derivedPullIso a (f' ≫ g)).app K) ((derivedPullIso a (g' ≫ f)).app K)
    (native_pull_comp a g' f K) (native_pull_comp a f' g K)
    (native_pull_eq a (f' ≫ g) (g' ≫ f) sq.toCommSq.w.symm K)
  exact replace_iso_rectangle (derivedScalars a X') _ _ _ _ _ _ _ _
    (comparison_app Λ sq K) (comparison_app Λ' sq ((derivedScalars a Y).obj K)) h

/-- Coefficient pullback comparisons commute with the canonical square comparison. -/
theorem flat_coefficient_pullback_cube
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : ChosenCartesianSquare g' f' f g) (K : DerivedCategory (Modules Λ Y)) :
    Adjunction.coefficientPullbackSquare
      (condensedAmbientPullbackComparison Λ sq).hom
      (condensedAmbientPullbackComparison Λ' sq).hom
      (derivedPullIso a f) (derivedPullIso a f')
      (derivedPullIso a g).hom (derivedPullIso a g').hom K := by
  exact pullback_square_of_iso _ _ _ _ _ _ K (native_pull_cube_iso a sq K)

end AlgebraicGeometry.ProEtale.RationalP1
