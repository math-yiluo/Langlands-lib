/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
import all WeilConjectures.AlgebraicGeometry.DerivedExchangeModuleTermwise
import all WeilConjectures.AlgebraicGeometry.UnboundedProperOpenComposition

/-!
# Unbounded proper/open AdjunctionNormalization

Source: Stacks Project, Tags 0F7B.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorObjQIso Functor.mapDerivedCategoryNatIso

private theorem ordinary_cartesian_support
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (sq : IsPullback r k i p)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _
        (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} A) sq)).inv)).app F ≫
      (p)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) =
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom.app F := by
  let B := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
    (ModuleCat.{u + 1} A) sq)
  have hb : B.inv.app ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app
        ((r)^*[ModuleCat.{u + 1} A].obj ((r)_*[ModuleCat.{u + 1} A].obj F)) =
      (p)^*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
          ((r)_*[ModuleCat.{u + 1} A].obj F)) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
          ((r)_*[ModuleCat.{u + 1} A].obj F) := by
    apply (cancel_epi (B.hom.app ((r)_*[ModuleCat.{u + 1} A].obj F))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact (openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
      (ModuleCat.{u + 1} A) sq.toCommSq _).symm
  have hm : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).unit.app
      ((i)_*[ModuleCat.{u + 1} A].obj ((r)_*[ModuleCat.{u + 1} A].obj F)) ≫
      (p)_*[ModuleCat.{u + 1} A].map
        ((baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
          ((r)_*[ModuleCat.{u + 1} A].obj F)) ≫
      (p)_*[ModuleCat.{u + 1} A].map ((k)_*[ModuleCat.{u + 1} A].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app F)) =
      (squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom.app F := by
    rw [← Category.assoc, unit_map_baseChangeMap_app]
    have hn := (squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom.naturality
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app F)
    simp only [Functor.comp_map] at hn
    erw [Category.assoc, ← hn,
      ← (i)_*[ModuleCat.{u + 1} A].map_comp_assoc,
      Adjunction.right_triangle_components, (i)_*[ModuleCat.{u + 1} A].map_id,
      Category.id_comp]
    rfl
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Functor.comp_obj, Functor.comp_map, Category.assoc]
  erw [Category.id_comp]
  rw [← (p)_*[ModuleCat.{u + 1} A].map_comp_assoc,
    ← (p)_*[ModuleCat.{u + 1} A].map_comp]
  have hn := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).naturality
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).counit.app F)
  simp only [Category.assoc]
  erw [hn, reassoc_of% hb]
  simp only [Functor.map_comp]
  have hu := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).unit.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
      ((r)_*[ModuleCat.{u + 1} A].obj F))
  simp only [Functor.id_map, Functor.comp_map] at hu
  erw [← reassoc_of% hu, hm]

private theorem ordinary_cartesian_compare
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (sq : IsPullback r k i p)
    (θ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
      (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (hθ : ∀ F, θ.hom.app F ≫
      (p)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
      (lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w.symm).hom.app F) :
    θ.hom = (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _
        (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} A) sq)).inv)) := by
  apply NatTrans.ext
  funext (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
  have := open_compare_mono A k F
  apply (cancel_mono ((p)_*[ModuleCat.{u + 1} A].map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F))).1
  let e : (p)_*[ModuleCat.{u + 1} A].obj ((k)_*[ModuleCat.{u + 1} A].obj F) ≅
      (r ≫ i)_*[ModuleCat.{u + 1} A].obj F :=
    (lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) k p (r ≫ i) sq.w).app F
  apply (CategoryTheory.cancel_mono e.hom).1
  dsimp only [e, Iso.app_hom]
  rw [Category.assoc, Category.assoc,
    reassoc_of% ordinary_cartesian_support.{u} A k r p i sq F]
  simp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hgen (h : U ⟶ Z) (hh : h = k ≫ p) :
      θ.hom.app F ≫ (p)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
        (lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) k p h hh).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
        (lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) r i h (hh.trans sq.w.symm)).hom.app F := by
    subst h
    exact hθ F
  exact hgen (r ≫ i) sq.w

set_option backward.isDefEq.respectTransparency false in
private theorem derived_cartesian_normalized
    {C₁ C₂ C₃ C₄ : Type v}
    [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃] [Category.{w} C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ H)
    (c : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hc : ProperOpenUnitNormalized R R' H G
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)) c) :
    c = (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso L H).symm).hom)) := by
  have : (R.rightDerivedFunctor ⋙ G.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorUnit G.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso C₁ (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
        G.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun X ↦ ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    have hi : IsIso (R.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C₁ (.up ℤ)).obj J)) := inferInstance
    change IsIso (G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C₁ (.up ℤ)).obj J)) ≫ 𝟙 _)
    infer_instance
  apply Functor.rightDerived_ext (R.rightDerivedFunctor ⋙ G.mapDerivedCategory)
    (Functor.whiskerRight R.rightDerivedFunctorUnit G.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso C₁ (.up ℤ))
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.comp_obj]
  simp only [Category.comp_id]
  erw [hc K]
  symm
  exact Adjunction.derivedExact_mateEquiv_app_fac adj adj'
    (TwoSquare.mk _ _ _ _ e.hom)
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso L H).symm).hom)
    (by
      intro N
      simpa only [Iso.trans_hom, Iso.symm_hom] using square_factors G L L' H e N) K

set_option backward.isDefEq.respectTransparency true in
/-- The support- and unit-normalized derived comparison on a Cartesian square
is the canonical adjunction exchange.
Source: Stacks Project, Tag 0F7B.
(auxiliary; not a blueprint node).

Proof:
The ordinary mate of the inverse open base-change map has the required support
normalization. This follows by composing with the inclusion of extension by zero
into direct image, using compatibility of open base change with this inclusion,
and applying naturality and the adjunction triangle identities. That inclusion is
monic, as is its proper direct image, so the given theta is this ordinary mate.
The unit formula for deriving an adjunction mate is then exactly the assumed
unit normalization of Gamma. Uniqueness of right-derived transformations identifies
Gamma with the descended mate, whose definition is the specified exchange.
-/
theorem etaleProperOpenCartesianNormalization
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback r k i p)
    (θ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
      (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (hθ : ∀ F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A), θ.hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) r i
              (k ≫ p) sq.toCommSq.flip.w).hom.app F)
    (Γ : R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))
    (hΓ : ProperOpenUnitNormalized
      (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
      (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A] θ.hom Γ.hom) :
    Γ.hom = openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq := by
  let B := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
    (ModuleCat.{u + 1} A) sq)
  have ht := ordinary_cartesian_compare A k r p i sq θ hθ
  have hd := derived_cartesian_normalized
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    B.symm Γ.hom
    (by
      dsimp only [B, Iso.symm_hom]
      rw [← ht]
      exact hΓ)
  simpa only [Category.assoc, openImmersionLowerShriekLowerStarExchange,
    mapDerivedUpperStarLowerStarAdjunction,
    mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso,
    Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, B] using hd

end AlgebraicGeometry.Etale
