/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
import all WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedOpenCounitSiteTransport

/-! # Identity factors in fixed-scalar compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The actual open/proper pair, without introducing a chosen compactification. -/
def identityFactorPair {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p] : Compactification (i ≫ p) where
  Z := Z
  i := i
  g := p
  comm := rfl
  isOpenImmersion := inferInstance
  isProper := inferInstance

/-- Remove the identity open extension in the proper compactification. -/
def identityFactorFixedProper (Λ : Type (u + 1)) [CommRing Λ]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsProper p) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekIdIso _ Z) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- Remove the identity direct image in the open compactification. -/
def identityFactorFixedOpen (Λ : Type (u + 1)) [CommRing Λ]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsOpenImmersion i) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (rightDerivedLowerStarId (ModuleCat.{u + 1} Λ) Z) ≪≫
    Functor.rightUnitor _

/-- The two identity-factor unit maps, in their order of application. -/
def identityFactorFixedIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsOpenImmersion i) ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsProper p) ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (identityFactorPair i p) :=
  Functor.isoWhiskerLeft _ (identityFactorFixedProper Λ p) ≪≫
    Functor.isoWhiskerRight (identityFactorFixedOpen Λ i) _

private def identityTriangle {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p] : Compactification.Triangle i p where
  cf := Compactification.ofIsOpenImmersion i
  cg := Compactification.ofIsProper p
  cfg := identityFactorPair i p
  q := 𝟙 Z
  p := 𝟙 Z
  i_q := Category.comp_id i
  p_g := Category.id_comp p
  isOpenImmersion_q := inferInstanceAs (IsOpenImmersion (𝟙 Z))
  isPullback := by
    change IsPullback (𝟙 Z) (𝟙 Z) (𝟙 Z) (𝟙 Z)
    exact IsPullback.of_horiz_isIso ⟨rfl⟩

attribute [local implicit_reducible] identityTriangle identityFactorPair
  Compactification.ofIsOpenImmersion Compactification.ofIsProper ExchangeFormalism.shriek
  coherenceBoundedSiteFunctor coherenceSiteFunctor Functor.mapDerivedCategoryPlus

private theorem identityTriangle_comp
    (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p] (K : F.obj X) :
    (F.compIso (identityTriangle i p)).hom.app K =
      (F.pf p).map ((F.shId Z).hom.app ((F.pf (𝟙 Z)).obj ((F.sh i).obj K))) ≫
        (F.pf p).map ((F.pfId Z).hom.app ((F.sh i).obj K)) := by
  have hw : 𝟙 Z ≫ 𝟙 Z = 𝟙 Z ≫ 𝟙 Z := rfl
  have : IsIso (F.baseChange (𝟙 Z) (𝟙 Z) (𝟙 Z) (𝟙 Z) hw) :=
    CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := F) (IsPullback.of_horiz_isIso ⟨hw⟩)
  have h₁ := congr_app (F.exchange_id_vert (𝟙 Z) hw) ((F.sh i).obj K)
  have h₂ := congr_app (F.shComp'_id_right i) K
  simp only [CategoryTheory.TwoSquare.whiskerLeft, CategoryTheory.TwoSquare.whiskerRight,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.comp_id,
    Functor.comp_obj, Functor.id_obj] at h₁ h₂
  rw [CompactSupportFormalism.compIso_hom_app]
  dsimp only [identityTriangle, Compactification.ofIsOpenImmersion,
    Compactification.ofIsProper, identityFactorPair]
  have hSC : (F.shComp' i (𝟙 Z) i (Category.comp_id i)).inv.app K =
      (F.shId Z).hom.app ((F.sh i).obj K) := by
    rw [← cancel_epi ((F.shComp' i (𝟙 Z) i (Category.comp_id i)).hom.app K),
      Iso.hom_inv_id_app]
    exact h₂.symm
  rw [h₁, hSC, F.pfComp'_id_left_inv_app]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private def identityOpenUnit (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} Λ) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

private theorem identityEtaleCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ Y)
    [IsOpenImmersion i] [IsProper p] [QuasiCompact i]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (coherenceEtaleCompositorComponent Λ (Compactification.ofIsOpenImmersion i)
        (Compactification.ofIsProper p) (identityFactorPair i p) L).hom =
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.map
        ((finiteSiteEtaleOpenId Λ Z).hom.app
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Z)).rightDerivedFunctorPlus.obj
            ((Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj L))) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.map
        ((Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) Z).hom.app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj L)) := by
  have h := etale_compositor_tower Λ (Compactification.ofIsOpenImmersion i)
    (Compactification.ofIsProper p) (identityFactorPair i p) (identityTriangle i p) L
  have h' : (coherenceEtaleCompositor Λ (Compactification.ofIsOpenImmersion i)
      (Compactification.ofIsProper p) (identityFactorPair i p)).hom.app L =
        ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).compIso
          (identityTriangle i p)).hom.app L := by
    simpa only [identityTriangle, coherenceEtaleChangeIso, coherenceEtaleFunctor,
      Etale.rightDerivedLowerShriekOfCompactificationPlusIso_refl,
      Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id, towerEtaleIso,
      Etale.native_bounded_triangle_iso_eq] using h
  rw [identityTriangle_comp, etale_open_id_eq, etale_proper_id_eq] at h'
  exact h'

private theorem identityDirectComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarComparisonIso' (𝟙 X) (ModuleCat.{u + 1} Λ)).hom.app K ≫
        (rightDerivedLowerStarId (ModuleCat.{u + 1} Λ) X).hom.app
          ((coherenceBoundedSiteFunctor Λ X).obj K) =
      (coherenceBoundedSiteFunctor Λ X).map
        ((Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app K) := by
  let B := ModuleCat.{u + 1} Λ
  let G := lowerStar B (𝟙 X)
  let N := comparisonUpperStar B X
  let U := Functor.rightDerivedFunctorPlusNatIso (lowerStarId B X) ≪≫
    Functor.rightDerivedFunctorPlusIdIso _
  have hu (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) B)) :
      G.rightDerivedFunctorPlusCompatibility.hom.app M ≫
          (rightDerivedLowerStarId B X).hom.app M.obj =
        DerivedCategory.Plus.ι.map (U.hom.app M) := by
    apply Functor.normalized_identity_compat G (lowerStarId B X)
      (rightDerivedLowerStarId B X) _ M
    intro T
    change G.rightDerivedFunctorUnit.app T ≫
      (Functor.rightDerivedFunctorNatTrans (lowerStarId B X).hom).app
        (DerivedCategory.Qh.obj T) ≫
      (Functor.rightDerivedFunctorIdIso _).hom.app (DerivedCategory.Qh.obj T) = _
    rw [Functor.rightDerivedFunctorNatTrans_app_assoc,
      Functor.rightDerivedFunctorIdIso_fac_app]
    erw [Category.comp_id]
  have hm := Functor.rightDerivedFunctorPlusBaseChange_id (Etale.lowerStarId B X)
    (lowerStarId B X) _ (lowerStarComparisonUpperStarBaseChange_app_id B X) K
  simp only [rightDerivedLowerStarComparisonIso',
    Functor.mapDerivedCategoryPlusCompatibility, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  change DerivedCategory.Plus.ι.map
      ((rightDerivedLowerStarComparisonPlusIso (𝟙 X) B).hom.app K) ≫
      G.rightDerivedFunctorPlusCompatibility.hom.app (N.mapDerivedCategoryPlus.obj K) ≫
        (rightDerivedLowerStarId B X).hom.app _ = _
  dsimp only [ObjectProperty.ι_obj]
  erw [hu]
  rw [← DerivedCategory.Plus.ι.map_comp]
  change DerivedCategory.Plus.ι.map
    ((Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange (𝟙 X) B)).app K ≫
        U.hom.app (N.mapDerivedCategoryPlus.obj K)) = _
  rw [hm]
  dsimp only [U, N]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rfl

private lemma identityAdjointIso {C : Type*} [Category C]
    {F G : C ⥤ C} (a : F ⊣ G) (e : G ≅ 𝟭 C) :
    a.leftAdjointUniq (Adjunction.id.ofNatIsoRight e.symm) = a.leftAdjointIdIso e := by
  apply Iso.ext
  ext M : 2
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateIsoEquiv, conjugateEquiv, Adjunction.ofNatIsoRight]

private theorem identityOpenComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (fixSiteOpenComparison Λ (𝟙 X)).hom.app K.obj ≫
        (identityOpenUnit Λ X).hom.app ((coherenceBoundedSiteFunctor Λ X).obj K) =
      (coherenceBoundedSiteFunctor Λ X).map
        ((finiteSiteEtaleOpenId Λ X).hom.app K) := by
  have h := congrArg DerivedCategory.Plus.ι.map
    ((finiteSiteWordRefinement Λ).2.2.2.2.2.2.2.2.1 X K)
  have he : DerivedCategory.Plus.ι.map
      ((properOpenSiteExtensionIso Λ (𝟙 X)).hom.app K) =
        (fixSiteOpenComparison Λ (𝟙 X)).hom.app K.obj :=
    inclusion_square_hom _ _ _ _
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) (𝟙 X)) K
  simpa only [Functor.map_comp, he, finiteSiteProEtaleOpenId, identityOpenUnit,
    openImmersionLowerShriekIdIso, identityAdjointIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app, coherenceBoundedSiteFunctor,
    Functor.comp_obj, Functor.comp_map, coherenceSiteFunctor, ObjectProperty.ι_obj, plus_obj_obj,
    inclusion_map] using h

-- The two primitive comparison identity laws paste by naturality alone.
private theorem identityFactorPaste
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (N : C ⥤ D) (M : E ⥤ F) (P : C ⥤ E) (Q : D ⥤ F)
    (j r : C ⥤ C) (J R : D ⥤ D)
    (b : P ⋙ M ≅ N ⋙ Q) (e : j ⋙ N ≅ N ⋙ J) (d : r ⋙ N ≅ N ⋙ R)
    (u : j ≅ 𝟭 C) (v : r ≅ 𝟭 C) (U : J ≅ 𝟭 D) (V : R ≅ 𝟭 D)
    (he : ∀ A, e.hom.app A ≫ U.hom.app (N.obj A) = N.map (u.hom.app A))
    (hd : ∀ A, d.hom.app A ≫ V.hom.app (N.obj A) = N.map (v.hom.app A))
    (A : C) (T : D) (a : N.obj A ⟶ T) :
    b.hom.app (j.obj (r.obj A)) ≫ Q.map (e.hom.app (r.obj A)) ≫
        Q.map (J.map (d.hom.app A ≫ R.map a)) ≫
        Q.map (U.hom.app (R.obj T)) ≫ Q.map (V.hom.app T) =
      M.map (P.map (u.hom.app (r.obj A)) ≫ P.map (v.hom.app A)) ≫
        b.hom.app A ≫ Q.map a := by
  have hU := U.hom.naturality (d.hom.app A ≫ R.map a)
  dsimp only [Functor.id_map, Functor.comp_obj] at hU
  have hV := V.hom.naturality a
  dsimp only [Functor.id_map] at hV
  have hp : b.hom.app (j.obj (r.obj A)) ≫
      Q.map (e.hom.app (r.obj A)) ≫ Q.map (U.hom.app (N.obj (r.obj A))) =
      M.map (P.map (u.hom.app (r.obj A))) ≫ b.hom.app (r.obj A) := by
    rw [← Q.map_comp, he]
    exact (b.hom.naturality (u.hom.app (r.obj A))).symm
  have ho : (d.hom.app A ≫ R.map a) ≫ V.hom.app T =
      N.map (v.hom.app A) ≫ a := by
    rw [Category.assoc, hV, ← Category.assoc, hd]
  have hUQ : Q.map (J.map (d.hom.app A ≫ R.map a)) ≫
      Q.map (U.hom.app (R.obj T)) =
      Q.map (U.hom.app (N.obj (r.obj A))) ≫ Q.map (d.hom.app A ≫ R.map a) := by
    rw [← Q.map_comp, hU, Q.map_comp]
  rw [reassoc_of% hUQ, reassoc_of% hp]
  rw [← Q.map_comp, ho, Q.map_comp]
  have hn := b.hom.naturality (v.hom.app A)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← M.map_comp_assoc]

private theorem identityFactorIsoApp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (j : C ⥤ D) (P : D ⥤ E) (J R : D ⥤ D)
    (U : J ≅ 𝟭 D) (V : R ≅ 𝟭 D) (K : C) :
    (Functor.isoWhiskerLeft (j ⋙ R)
        (Functor.isoWhiskerRight U P ≪≫ Functor.leftUnitor P) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft j V ≪≫ Functor.rightUnitor j) P).hom.app K =
      P.map (U.hom.app (R.obj (j.obj K))) ≫ P.map (V.hom.app (j.obj K)) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id, Category.comp_id]
  rfl

attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

/-- The geometric compositor on an etale-origin input is the pair of identity unit maps.
This statement involves no intrinsic coefficient presentation or retained finite witness. -/
theorem identityFactorFixedCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    (i : X ⟶ Z) (p : Z ⟶ Y) [IsOpenImmersion i] [IsProper p] [QuasiCompact i]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    coherenceProEtaleCompositor Λ (Compactification.ofIsOpenImmersion i)
        (Compactification.ofIsProper p) (identityFactorPair i p) L =
      (identityFactorFixedIso Λ i p).hom.app ((coherenceBoundedSiteFunctor Λ X).obj L) := by
  let B := ModuleCat.{u + 1} Λ
  let e : (Etale.openImmersionLowerShriek B (𝟙 Z)).mapDerivedCategoryPlus ⋙
      coherenceBoundedSiteFunctor Λ Z ≅
      coherenceBoundedSiteFunctor Λ Z ⋙
        (openImmersionLowerShriek B (𝟙 Z)).mapDerivedCategory :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι (fixSiteOpenComparison Λ (𝟙 Z))
  have h := identityFactorPaste
    (coherenceBoundedSiteFunctor Λ Z) (coherenceBoundedSiteFunctor Λ Y)
    (Etale.lowerStar B p).rightDerivedFunctorPlus (lowerStar B p).rightDerivedFunctor
    (Etale.openImmersionLowerShriek B (𝟙 Z)).mapDerivedCategoryPlus
    (Etale.lowerStar B (𝟙 Z)).rightDerivedFunctorPlus
    (openImmersionLowerShriek B (𝟙 Z)).mapDerivedCategory
    (lowerStar B (𝟙 Z)).rightDerivedFunctor
    (rightDerivedLowerStarComparisonIso' p B) e
    (rightDerivedLowerStarComparisonIso' (𝟙 Z) B)
    (finiteSiteEtaleOpenId Λ Z) (Etale.lowerStarIdDerivedPlus B Z)
    (identityOpenUnit Λ Z) (rightDerivedLowerStarId B Z)
    (identityOpenComparison Λ Z) (identityDirectComparison Λ Z)
    ((Etale.openImmersionLowerShriek B i).mapDerivedCategoryPlus.obj L)
    ((openImmersionLowerShriek B i).mapDerivedCategory.obj
      ((coherenceBoundedSiteFunctor Λ X).obj L))
    ((fixSiteOpenComparison Λ i).hom.app L.obj)
  have hunit := identityFactorIsoApp
    (openImmersionLowerShriek B i).mapDerivedCategory (lowerStar B p).rightDerivedFunctor
    (openImmersionLowerShriek B (𝟙 Z)).mapDerivedCategory
    (lowerStar B (𝟙 Z)).rightDerivedFunctor
    (identityOpenUnit Λ Z) (rightDerivedLowerStarId B Z)
    ((coherenceBoundedSiteFunctor Λ X).obj L)
  change (identityFactorFixedIso Λ i p).hom.app _ = _ at hunit
  apply (cancel_epi (coherenceCompositionSource Λ
    (Compactification.ofIsOpenImmersion i) (Compactification.ofIsProper p) L).hom).mp
  rw [← composition_site_square, identityEtaleCompositor, hunit]
  symm
  simp only [coherenceCompositionSource, coherenceBoundaryComponent,
    coherenceEvaluateSquare, coherenceBoundaryIso, compactComparison_hom,
    identityOpenUnit, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.map_comp,
    coherenceProEtaleFunctor, rightDerivedLowerShriekOfCompactification,
    Compactification.ofIsOpenImmersion, Compactification.ofIsProper, identityFactorPair,
    coherenceEtaleFunctor, Etale.rightDerivedLowerShriekOfCompactificationPlus,
    Functor.comp_obj, Functor.comp_map, Category.assoc, B, e, ObjectProperty.ι_obj,
    plus_obj_obj] at h ⊢
  exact h

end AlgebraicGeometry.ProEtale
