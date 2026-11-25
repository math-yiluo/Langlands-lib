/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar

/-! Compactification-level proper compositor and forget-supports calculation.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

universe vC vD vE uC uD uE wC wD wE

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryAdjunction
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma exact_unit_ext
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {F G : DerivedCategory C ⥤ DerivedCategory C} {α β : F ⟶ G}
    (h : ∀ K : HomotopyCategory C (.up ℤ),
      α.app (DerivedCategory.Qh.obj K) = β.app (DerivedCategory.Qh.obj K)) : α = β := by
  exact Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) h

private lemma exact_adj_comp
    {C : Type uC} {D : Type uD} {E : Type uE} [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    [Abelian C] [Abelian D] [Abelian E]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D] [IsGrothendieckAbelian.{vE} E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wE} E]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) :
    (a.comp b).mapDerivedCategoryAdjunction =
      ((a.mapDerivedCategoryAdjunction.comp b.mapDerivedCategoryAdjunction
        ).ofNatIsoLeft (Functor.mapDerivedCategoryCompIso L₁ L₂)
          ).ofNatIsoRight (Functor.mapDerivedCategoryCompIso R₂ R₁) := by
  apply Adjunction.ext
  apply exact_unit_ext (C := C)
  intro K
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_unit_app]
  let KL := ((L₁ ⋙ L₂).mapHomotopyCategory (.up ℤ)).obj K
  rw [← cancel_mono ((R₂ ⋙ R₁).mapDerivedCategory.map
    ((L₁ ⋙ L₂).mapDerivedCategoryFactorsh.hom.app K) ≫
      (R₂ ⋙ R₁).mapDerivedCategoryFactorsh.hom.app KL)]
  simp only [Category.assoc]
  rw [(a.comp b).mapDerivedCategoryAdjunction_unit_app_fac K]
  have hL : (Functor.mapDerivedCategoryCompIso L₁ L₂).hom.app
      (DerivedCategory.Qh.obj K) ≫ (L₁ ⋙ L₂).mapDerivedCategoryFactorsh.hom.app K =
      L₂.mapDerivedCategory.map (L₁.mapDerivedCategoryFactorsh.hom.app K) ≫
        L₂.mapDerivedCategoryFactorsh.hom.app ((L₁.mapHomotopyCategory (.up ℤ)).obj K) := by
    rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso L₁ L₂).inv.app
      (DerivedCategory.Qh.obj K)), Iso.inv_hom_id_app_assoc]
    exact (Functor.mapDerivedCategoryCompIso_hom_app_factorsh L₁ L₂ K).symm
  have hR : (Functor.mapDerivedCategoryCompIso R₂ R₁).hom.app
      (DerivedCategory.Qh.obj KL) ≫ (R₂ ⋙ R₁).mapDerivedCategoryFactorsh.hom.app KL =
      R₁.mapDerivedCategory.map (R₂.mapDerivedCategoryFactorsh.hom.app KL) ≫
        R₁.mapDerivedCategoryFactorsh.hom.app ((R₂.mapHomotopyCategory (.up ℤ)).obj KL) := by
    rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso R₂ R₁).inv.app
      (DerivedCategory.Qh.obj KL)), Iso.inv_hom_id_app_assoc]
    exact (Functor.mapDerivedCategoryCompIso_hom_app_factorsh R₂ R₁ KL).symm
  have hn := (Functor.mapDerivedCategoryCompIso R₂ R₁).hom.naturality
    ((L₁ ⋙ L₂).mapDerivedCategoryFactorsh.hom.app K)
  simp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  rw [hR]
  simp only [Functor.comp_map]
  slice_rhs 3 4 =>
    erw [← R₁.mapDerivedCategory.map_comp, ← R₂.mapDerivedCategory.map_comp, hL]
  simp only [Functor.map_comp, Category.assoc]
  have hη := b.mapDerivedCategoryAdjunction.unit.naturality
    (L₁.mapDerivedCategoryFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.id_map] at hη
  slice_rhs 2 3 =>
    erw [← R₁.mapDerivedCategory.map_comp, ← hη]
  simp only [Functor.map_comp, Category.assoc]
  slice_rhs 3 5 =>
    erw [← R₁.mapDerivedCategory.map_comp_assoc,
      ← R₁.mapDerivedCategory.map_comp, Category.assoc,
      b.mapDerivedCategoryAdjunction_unit_app_fac]
  have hN := R₁.mapDerivedCategoryFactorsh.hom.naturality
    ((b.mapHomotopyCategory (.up ℤ)).unit.app ((L₁.mapHomotopyCategory (.up ℤ)).obj K))
  simp only [Functor.comp_map] at hN
  erw [hN]
  erw [reassoc_of% (a.mapDerivedCategoryAdjunction_unit_app_fac K)]
  rw [← Functor.map_comp]
  congr 1
  rw [Adjunction.mapHomotopyCategory_comp_unit_app]
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.comp_id]
private lemma exact_adj_conjugate
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂) (r : R₂ ≅ R₁)
    (h : ∀ K, a.unit.app K ≫ R₁.map (e.hom.app K) =
      b.unit.app K ≫ r.hom.app (L₂.obj K)) :
    a.mapDerivedCategoryAdjunction.unit ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom R₁.mapDerivedCategory =
      b.mapDerivedCategoryAdjunction.unit ≫
        Functor.whiskerLeft L₂.mapDerivedCategory (Functor.mapDerivedCategoryNatIso r).hom := by
  apply exact_unit_ext (C := C)
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (R₁.mapDerivedCategory.map (L₂.mapDerivedCategoryFactorsh.hom.app K) ≫
    R₁.mapDerivedCategoryFactorsh.hom.app ((L₂.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  have he := Functor.mapDerivedCategoryNatIso_fach e K
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, he, Functor.map_comp]
  have hNR := R₁.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K)
  simp only [Functor.comp_map] at hNR
  simp only [Category.assoc]
  erw [hNR]
  erw [reassoc_of% (a.mapDerivedCategoryAdjunction_unit_app_fac K)]
  have hN := (Functor.mapDerivedCategoryNatIso r).hom.naturality
    (L₂.mapDerivedCategoryFactorsh.hom.app K)
  erw [← reassoc_of% hN]
  erw [Functor.mapDerivedCategoryNatIso_fach r]
  erw [reassoc_of% (b.mapDerivedCategoryAdjunction_unit_app_fac K)]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ) a b e.hom r.hom h K
private lemma derived_open_comp_conjugate
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) [IsOpenImmersion j₁] [IsOpenImmersion j₂] :
    conjugateEquiv
      ((openImmersionLowerShriekUpperStarAdjunction B j₁
        ).mapDerivedCategoryAdjunction.comp
        (openImmersionLowerShriekUpperStarAdjunction B j₂
          ).mapDerivedCategoryAdjunction)
      (openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
        ).mapDerivedCategoryAdjunction
      (Functor.mapDerivedCategoryTriangleIso
        (openImmersionLowerShriekComp B j₁ j₂)).hom =
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp B j₁ j₂)).inv := by
  let a := openImmersionLowerShriekUpperStarAdjunction B j₁
  let b := openImmersionLowerShriekUpperStarAdjunction B j₂
  let c := openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
  let e := openImmersionLowerShriekComp B j₁ j₂
  let r := upperStarComp B j₁ j₂
  have hu (K : Sheaf X.smallEtaleTopology B) :
      c.unit.app K ≫ (upperStar B (j₁ ≫ j₂)).map (e.hom.app K) =
        (a.comp b).unit.app K ≫ r.inv.app
          (((openImmersionLowerShriek B j₁) ⋙ (openImmersionLowerShriek B j₂)).obj K) := by
    exact Adjunction.unit_leftAdjointUniq_hom_app c ((a.comp b).ofNatIsoRight r.symm) K
  have hd := exact_adj_conjugate
    (C := Sheaf X.smallEtaleTopology B) (D := Sheaf Z.smallEtaleTopology B)
    c (a.comp b) e r.symm hu
  rw [exact_adj_comp (C := Sheaf X.smallEtaleTopology B)
    (D := Sheaf Y.smallEtaleTopology B) (E := Sheaf Z.smallEtaleTopology B) a b] at hd
  apply conjugateEquiv_eq_of_unit
  intro K
  have hK := congrArg (fun t ↦ t.app K) hd
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_unit_app,
    Functor.mapDerivedCategoryNatIso_symm] at hK
  let L₁ := openImmersionLowerShriek B j₁
  let L₂ := openImmersionLowerShriek B j₂
  let R := upperStar B (j₁ ≫ j₂)
  let R₁ := upperStar B j₁
  let R₂ := upperStar B j₂
  have hk := congrArg (fun t ↦ t ≫ R.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso L₁ L₂).inv.app K)) hK
  simp only [Category.assoc] at hk
  have hn := (Functor.mapDerivedCategoryTriangleIso r).inv.naturality
    ((Functor.mapDerivedCategoryCompIso L₁ L₂).inv.app K)
  simp only [Functor.comp_map] at hn
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc] at hn
  erw [← hn] at hk
  erw [← (R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory).map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hk
  simpa only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Adjunction.comp_unit_app,
    a, b, c, e, r, L₁, L₂, R, R₁, R₂, Category.assoc] using hk.symm

private lemma open_compare_comp
    (A : Type (u + 1)) [CommRing A]
    {U V W : Scheme.{u}} (k : U ⟶ V) (i : V ⟶ W)
    [IsOpenImmersion k] [IsOpenImmersion i] (F : DerivedCategoryModule A U) :
    (derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (k ≫ i)).app F =
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) k i).hom.app F ≫
      (derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj F) ≫
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) k i).hom.app F := by
  let B := ModuleCat.{u + 1} A
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction B k
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction B i
  let c := derivedOpenImmersionLowerShriekUpperStarAdjunction B (k ≫ i)
  let r := Functor.mapDerivedCategoryNatIso (upperStarComp B k i) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  let e := mapDerivedCategoryOpenImmersionLowerShriekComp B k i
  have hu := unit_conjugateEquiv (a.comp b) c e.hom F
  have he := derived_open_comp_conjugate B k i
  change conjugateEquiv (a.comp b) c e.hom = r.inv at he
  rw [he] at hu
  have hr : (rightDerivedLowerStarComp B k i).hom =
      conjugateEquiv ((mapDerivedUpperStarLowerStarAdjunction B i).comp
        (mapDerivedUpperStarLowerStarAdjunction B k))
        (mapDerivedUpperStarLowerStarAdjunction B (k ≫ i)) r.hom := by
    rfl
  have ht {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
      (N : DerivedCategoryModule A X) :
      (upperStar B j).mapDerivedCategory.map
          ((derivedOpenImmersionLowerShriekToLowerStar B j).app N) ≫
        (mapDerivedUpperStarLowerStarAdjunction B j).counit.app N =
      inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction B j).unit.app N) := by
    rw [derivedOpenImmersionLowerShriekToLowerStar_app, Adjunction.homEquiv_unit]
    rw [Functor.map_comp, Category.assoc]
    erw [(mapDerivedUpperStarLowerStarAdjunction B j).counit_naturality]
    rw [← Category.assoc]
    erw [(mapDerivedUpperStarLowerStarAdjunction B j).left_triangle_components]
    exact Category.id_comp _
  apply ((mapDerivedUpperStarLowerStarAdjunction B (k ≫ i)).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [ht, ← cancel_epi (c.unit.app F), IsIso.hom_inv_id]
  symm
  rw [← Category.assoc, ← hu]
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc]
  rw [hr]
  have hc := conjugateEquiv_counit
    ((mapDerivedUpperStarLowerStarAdjunction B i).comp
      (mapDerivedUpperStarLowerStarAdjunction B k))
    (mapDerivedUpperStarLowerStarAdjunction B (k ≫ i)) r.hom F
  simp only [Adjunction.comp_counit_app] at hc
  rw [← reassoc_of% r.inv.naturality, ← reassoc_of% r.inv.naturality]
  rw [hc]
  erw [r.inv_hom_id_app_assoc]
  have hn := (mapDerivedUpperStarLowerStarAdjunction B i).counit.naturality
    ((derivedOpenImmersionLowerShriekToLowerStar B k).app F)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hkn := congrArg ((upperStar B k).mapDerivedCategory.map) hn
  simp only [Functor.map_comp] at hkn
  rw [reassoc_of% hkn]
  have hz := congrArg ((upperStar B k).mapDerivedCategory.map)
    (ht i ((openImmersionLowerShriek B k).mapDerivedCategory.obj F))
  simp only [Functor.map_comp] at hz
  rw [reassoc_of% hz]
  simp only [← Functor.map_comp_assoc, ht]
  dsimp only [a, b]
  simp only [IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private lemma exchange_inclusion
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion b] [IsOpenImmersion i] (sq : IsPullback q b i p)
    (M : DerivedCategoryModule A U) :
    (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) b).app M) ≫
      (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) b p
        (q ≫ i) sq.w.symm).hom.app M =
    (derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.obj M) ≫
      (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) q i (q ≫ i) rfl).hom.app M := by
  let B := ModuleCat.{u + 1} A
  let bc := derivedOpenImmersionLowerShriekBaseChangeIso B sq
  let sigma := rightDerivedLowerStarCompIsoOfComp B q i (q ≫ i) rfl ≪≫
    (rightDerivedLowerStarCompIsoOfComp B b p (q ≫ i) sq.w.symm).symm
  have hn (N : DerivedCategoryModule A W) :
      bc.inv.app N ≫ (derivedOpenImmersionLowerShriekToLowerStar B b).app
          ((upperStar B q).leftDerivedFunctor.obj N) =
        (upperStar B p).leftDerivedFunctor.map
          ((derivedOpenImmersionLowerShriekToLowerStar B i).app N) ≫
        (derivedBaseChangeMap B sq.toCommSq).app N := by
    apply (cancel_epi (bc.hom.app N)).1
    rw [Iso.hom_inv_id_app_assoc]
    exact (derivedOpenImmersionLowerShriekBaseChangeIso_hom_comp_toLowerStar B sq N).symm
  have hm : (mateEquiv (derivedUpperStarLowerStarAdjunction B q)
      (derivedUpperStarLowerStarAdjunction B p)
      (derivedBaseChangeSquare B sq.toCommSq)) = sigma.hom := by
    rw [derivedBaseChangeSquare, iterated_mateEquiv_conjugateEquiv]
    change conjugateEquiv _ _
      ((leftDerivedUpperStarComp B b p (q ≫ i) sq.w).inv ≫
        (leftDerivedUpperStarComp B q i).hom) = _
    rw [← conjugateEquiv_comp _ (derivedUpperStarLowerStarAdjunction B (q ≫ i))]
    rfl
  have hx : (openImmersionLowerShriekLowerStarExchange B sq).app M =
      (derivedUpperStarLowerStarAdjunction B p).unit.app _ ≫
        (lowerStar B p).rightDerivedFunctor.map
          (bc.inv.app _ ≫ (openImmersionLowerShriek B b).mapDerivedCategory.map
            ((derivedUpperStarLowerStarAdjunction B q).counit.app M)) := by
    simp only [openImmersionLowerShriekLowerStarExchange_app,
      mapDerivedUpperStarLowerStarAdjunction_eq, Adjunction.ofNatIsoLeft_unit,
      Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
    simp only [bc, derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.map_comp, Category.assoc]
  have hs := (derivedOpenImmersionLowerShriekToLowerStar B b).naturality
    ((derivedUpperStarLowerStarAdjunction B q).counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hs
  have hbase : (openImmersionLowerShriekLowerStarExchange B sq).app M ≫
      (lowerStar B p).rightDerivedFunctor.map
        ((derivedOpenImmersionLowerShriekToLowerStar B b).app M) =
      (derivedOpenImmersionLowerShriekToLowerStar B i).app
        ((lowerStar B q).rightDerivedFunctor.obj M) ≫ sigma.hom.app M := by
    rw [hx, Category.assoc, ← Functor.map_comp, Category.assoc]
    erw [hs]
    rw [← Category.assoc, hn, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% (derivedUpperStarLowerStarAdjunction B p).unit.naturality
      ((derivedOpenImmersionLowerShriekToLowerStar B i).app
        ((lowerStar B q).rightDerivedFunctor.obj M))]
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map]
    have hmM := congr_app hm M
    simpa [derivedBaseChangeSquare, derivedBaseChangeMap, mateEquiv_apply,
      Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ (derivedOpenImmersionLowerShriekToLowerStar B i).app
        ((lowerStar B q).rightDerivedFunctor.obj M) ≫ t) hmM
  rw [reassoc_of% hbase]
  simp only [sigma, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Iso.inv_hom_id_app, Category.comp_id]

private lemma star_comp_hom
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) g h).hom =
      rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) g h (g ≫ h) rfl := by
  symm
  exact conjugateEquiv_leftDerivedUpperStarComp_hom _ g h (g ≫ h) rfl

private lemma open_compare_comp_congr
    (A : Type (u + 1)) [CommRing A]
    {U V W : Scheme.{u}} (k : U ⟶ V) (i : V ⟶ W) (j : U ⟶ W)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    (h : k ≫ i = j) (F : DerivedCategoryModule A U) :
    (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) k i).inv.app F ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) h).hom.app F ≫
      (derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app F =
      (derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj F) ≫
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) k i j h.symm).app F := by
  subst j
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rw [open_compare_comp, Iso.inv_hom_id_app_assoc, star_comp_hom]

private lemma star_comp_iso_hom
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ Z) (w : g ≫ h = k) :
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) g h k w).hom =
      rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) g h k w.symm := rfl

attribute [local irreducible] CategoryTheory.conjugateEquiv
  leftDerivedUpperStarComp derivedUpperStarLowerStarAdjunction
  derivedOpenImmersionLowerShriekToLowerStar openImmersionLowerShriekLowerStarExchange
  mapDerivedCategoryOpenImmersionLowerShriekComp mapDerivedCategoryOpenImmersionLowerShriekCongr

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Forget supports commutes with composition on compatible compactifications.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, first triangle, common pullback counits.

Proof: expand the compatible compositor into the open/proper exchange, the composition
of open extensions, and the ordinary proper direct-image compositor. Move the open
forget-supports map across exchange using its adjunction-unit mate equation. Composition
of the two open forget-supports maps is the forget-supports map for their composite,
by the composite counit formula and uniqueness of adjoints. Naturality and associativity
of the ordinary direct-image compositor then identify the remaining three proper
pushforward factors with the displayed compositor for p and f. The equality
`e.restrict.i ≫ pullback.fst e.g d.i = e.i` removes the final open congruence.
This calculation has no comparison between different compactifications.
(auxiliary; not a blueprint node)
-/
theorem properShriekComp_compactificationForgetSupports {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f]
    (d : Compactification f) (e : Compactification (p ≫ d.i))
    (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app E ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) (d.comp e)).app E =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A) e.restrict).app E) ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) d).app
          ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f (p ≫ f) rfl).hom.app E := by
  let B := ModuleCat.{u + 1} A
  simp only [rightDerivedLowerShriekOfCompactificationCompIso,
    compactificationForgetSupports, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, asIso_hom,
    Functor.comp_map, Functor.map_comp, Category.id_comp, Category.assoc,
    star_comp_iso_hom]
  have ho := open_compare_comp_congr A e.restrict.i (pullback.fst e.g d.i)
    e.i e.restrict_i_fst E
  have ho' := congrArg (fun t ↦ (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor.map t) ho
  simp only [Functor.map_comp] at ho'
  erw [reassoc_of% ho']
  erw [← (rightDerivedLowerStarComp B e.g d.g).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [star_comp_hom]
  erw [← (rightDerivedLowerStarCompHom B e.g d.g (e.g ≫ d.g) rfl).naturality_assoc,
    ← (rightDerivedLowerStarCompHom B e.g d.g (e.g ≫ d.g) rfl).naturality_assoc]
  simp only [Functor.comp_map]
  have h1 := rightDerivedLowerStarCompHom_assoc_app B e.i e.g d.g
    (p ≫ d.i) (e.g ≫ d.g) (p ≫ f) e.comm rfl
    (by rw [Category.assoc, ← d.comm]) E
  erw [h1]
  have h2 := rightDerivedLowerStarCompHom_assoc_app B e.restrict.i
    (pullback.fst e.g d.i) e.g e.i (e.restrict.g ≫ d.i) (p ≫ d.i)
    e.restrict_i_fst.symm e.isPullback_restrict.w e.comm E
  have h2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) h2
  simp only [Functor.map_comp] at h2'
  erw [← reassoc_of% h2']
  have hn := (rightDerivedLowerStarCompHom B (pullback.fst e.g d.i) e.g
    (e.restrict.g ≫ d.i) e.isPullback_restrict.w).naturality
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E)
  have hn' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hn
  simp only [Functor.comp_map, Functor.map_comp] at hn'
  erw [reassoc_of% hn']
  have hx := exchange_inclusion A (pullback.fst e.g d.i) e.restrict.g e.g d.i
    e.isPullback_restrict ((openImmersionLowerShriek B e.restrict.i).mapDerivedCategory.obj E)
  have hx' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hx
  simp only [Functor.map_comp, star_comp_iso_hom] at hx'
  erw [reassoc_of% hx']
  have hn2 := (rightDerivedLowerStarCompHom B e.restrict.g d.i
    (e.restrict.g ≫ d.i) rfl).naturality
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E)
  have hn2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hn2
  simp only [Functor.comp_map, Functor.map_comp] at hn2'
  erw [← reassoc_of% hn2']
  have h3 := rightDerivedLowerStarCompHom_assoc_app B e.restrict.i e.restrict.g d.i
    p (e.restrict.g ≫ d.i) (p ≫ d.i) e.restrict.comm rfl rfl E
  have h3' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) h3
  simp only [Functor.map_comp] at h3'
  erw [reassoc_of% h3']
  have ht1 := (derivedOpenImmersionLowerShriekToLowerStar B d.i).naturality
    ((lowerStar B e.restrict.g).rightDerivedFunctor.map
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E))
  have ht1' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) ht1
  simp only [Functor.map_comp] at ht1'
  erw [← reassoc_of% ht1']
  have ht2 := (derivedOpenImmersionLowerShriekToLowerStar B d.i).naturality
    ((rightDerivedLowerStarCompHom B e.restrict.i e.restrict.g p e.restrict.comm).app E)
  have ht2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) ht2
  simp only [Functor.map_comp] at ht2'
  erw [← reassoc_of% ht2']
  have h4 := rightDerivedLowerStarCompHom_assoc_app B p d.i d.g
    (p ≫ d.i) f (p ≫ f) rfl d.comm
    (by rw [Category.assoc, ← d.comm]) E
  erw [← h4]

end AlgebraicGeometry.Etale
