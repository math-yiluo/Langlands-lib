/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar

/-! # Transport of localization through the finite-coefficient realization equivalence

The functors and scalar comparison are explicit transports across an equivalence.

## References

* Stacks Project, Tags 03CY, 03D2, 03D3 and 0D6D
* Stacks Tags 03CY, 03DA and 03D3
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace LisseTowerLocalizationTransport

/-- Transport a functor through the unit of an equivalence. -/
def realizationLevel
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) [F.IsEquivalence] (K : C ⥤ E) :
    K ≅ F ⋙ (F.inv ⋙ K) := (F.asEquivalence.funInvIdAssoc K).symm

/-- Extend the scalar face uniquely along the fully faithful equivalence. -/
def realizationScalar
    {C₀ C₁ D₀ D₁ E₀ E₁ B : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [Category E₀] [Category E₁] [Category B]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) [F₀.IsEquivalence] [F₁.IsEquivalence]
    (K₀ : C₀ ⥤ E₀) (K₁ : C₁ ⥤ E₁) (H₀ : E₀ ⥤ B) (H₁ : E₁ ⥤ B)
    (q : C₀ ⥤ C₁) (Q : D₀ ⥤ D₁)
    (r : q ⋙ F₁ ≅ F₀ ⋙ Q) (k : q ⋙ K₁ ⋙ H₁ ≅ K₀ ⋙ H₀) :
    Q ⋙ (F₁.inv ⋙ K₁) ⋙ H₁ ≅ (F₀.inv ⋙ K₀) ⋙ H₀ := by
  let b₀ := realizationLevel F₀ K₀
  let b₁ := realizationLevel F₁ K₁
  apply ((Functor.whiskeringLeft C₀ D₀ B).obj F₀).preimageIso
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight r.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft q ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight b₁.symm H₁) ≪≫ k ≪≫
    Functor.isoWhiskerRight b₀ H₀ ≪≫ Functor.associator _ _ _

/-- Naturality and the defining preimage equation give the transported scalar square. -/
theorem realizationScalar_comm
    {C₀ C₁ D₀ D₁ E₀ E₁ B : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [Category E₀] [Category E₁] [Category B]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) [F₀.IsEquivalence] [F₁.IsEquivalence]
    (K₀ : C₀ ⥤ E₀) (K₁ : C₁ ⥤ E₁) (H₀ : E₀ ⥤ B) (H₁ : E₁ ⥤ B)
    (q : C₀ ⥤ C₁) (Q : D₀ ⥤ D₁)
    (r : q ⋙ F₁ ≅ F₀ ⋙ Q) (k : q ⋙ K₁ ⋙ H₁ ≅ K₀ ⋙ H₀)
    {C : C₁} {C' : C₀} (δ : C ⟶ q.obj C') :
    H₁.map (K₁.map δ) ≫ k.hom.app C' ≫
        H₀.map ((realizationLevel F₀ K₀).hom.app C') =
      H₁.map ((realizationLevel F₁ K₁).hom.app C) ≫
        ((F₁.inv ⋙ K₁) ⋙ H₁).map (F₁.map δ ≫ r.hom.app C') ≫
        (realizationScalar F₀ F₁ K₀ K₁ H₀ H₁ q Q r k).hom.app (F₀.obj C') := by
  have hs := congrArg (fun α ↦ α.app C')
    (((Functor.whiskeringLeft C₀ D₀ B).obj F₀).map_preimage
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight r.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft q ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (realizationLevel F₁ K₁).symm H₁) ≪≫ k ≪≫
        Functor.isoWhiskerRight (realizationLevel F₀ K₀) H₀ ≪≫
        Functor.associator _ _ _).hom)
  change (realizationScalar F₀ F₁ K₀ K₁ H₀ H₁ q Q r k).hom.app (F₀.obj C') = _ at hs
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp, Category.comp_id] at hs
  let M := (F₁.inv ⋙ K₁) ⋙ H₁
  have hr : M.map (r.hom.app C') ≫ M.map (r.inv.app C') = 𝟙 _ := by
    rw [← M.map_comp, Iso.hom_inv_id_app, M.map_id]
  have hb : H₁.map ((realizationLevel F₁ K₁).hom.app (q.obj C')) ≫
      H₁.map ((realizationLevel F₁ K₁).inv.app (q.obj C')) = 𝟙 _ := by
    rw [← H₁.map_comp, Iso.hom_inv_id_app, H₁.map_id]
  rw [hs]
  repeat erw [Category.id_comp]
  rw [M.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (M.map (r.hom.app C')) (M.map (r.inv.app C')), hr,
    Category.id_comp]
  dsimp only [M, Functor.comp_map]
  have hn := congrArg H₁.map ((realizationLevel F₁ K₁).hom.naturality δ)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp] at hn
  rw [← Category.assoc (H₁.map ((realizationLevel F₁ K₁).hom.app C)), ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc
    (H₁.map ((realizationLevel F₁ K₁).hom.app (q.obj C')))
    (H₁.map ((realizationLevel F₁ K₁).inv.app (q.obj C'))), hb, Category.id_comp]

end LisseTowerLocalizationTransport

open LisseTowerLocalizationTransport

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicFiniteProjection lisseTowerPulledScalarIso
  lisseTowerFixedScalarIso lisseTowerEtaleScalarIso localProEtaleNormalization

/-- Fixed-coefficient inverse image along two successive maps, followed by realization. -/
def lisseTowerLocalizationFixed {X Z S T : Scheme.{u}} (s : T ⟶ X)
    (a : T ⟶ S) (b : S ⟶ Z) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).mapDerivedCategory ⋙
    (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a).mapDerivedCategory ⋙
      lisseTowerFixedRealization s d n

/-- Transport fixed-coefficient inverse image through the explicit realization equivalence. -/
def lisseTowerLocalizationPull {X Z S T : Scheme.{u}} (t : Z ⟶ X) (s : T ⟶ X)
    (a : T ⟶ S) (b : S ⟶ Z) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  (lisseTowerFixedRealization t d n).inv ⋙ lisseTowerLocalizationFixed s a b d n

/-- The fixed-site level comparison before etale comparison. -/
def lisseTowerLocalizationFixedLevel {X Z S T : Scheme.{u}} (t : Z ⟶ X) (s : T ⟶ X)
    (a : T ⟶ S) (b : S ⟶ Z) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    lisseTowerLocalizationFixed s a b d n ≅
      lisseTowerFixedRealization t d n ⋙ lisseTowerLocalizationPull t s a b d n :=
  realizationLevel _ _

/-- The unit of realization gives the natural level comparison. -/
def lisseTowerLocalizationLevel {X Z S T : Scheme.{u}} (t : Z ⟶ X) (s : T ⟶ X)
    (a : T ⟶ S) (b : S ⟶ Z) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    localProEtaleComparison b (lisseTowerEtaleRing d n) ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a).mapDerivedCategory ⋙
          lisseTowerFixedRealization s d n ≅
      lisseTowerEtaleRealization t d n ⋙ lisseTowerLocalizationPull t s a b d n :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (lisseTowerLocalizationFixedLevel t s a b d n) ≪≫
    (Functor.associator _ _ _).symm

/-- Paste the coefficient mate for the first map with the pulled scalar square. -/
def lisseTowerLocalizationFixedScalar {X Z S T : Scheme.{u}} (s : T ⟶ X)
    (a : T ⟶ S) (b : S ⟶ Z) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    normalizationRestrict (ProEt.topology Z) (lisseTowerEtaleQuotient d n) ⋙
        lisseTowerLocalizationFixed s a b d (n + 1) ⋙
          pbcDerivedRestrict (constantAdicFiniteProjection s d (n + 1)) ≅
      lisseTowerLocalizationFixed s a b d n ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection s d n) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (localIsomorphismProEtaleCoefficients b (lisseTowerEtaleQuotient d n)) _ ≪≫
      Functor.associator _ _ _) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (lisseTowerPulledScalarIso s a d n) ≪≫
    (Functor.associator _ _ _).symm

/-- The scalar face is transported through the fully faithful realization equivalence. -/
def lisseTowerLocalizationScalar {X Z S T : Scheme.{u}} (t : Z ⟶ X) (s : T ⟶ X)
    (a : T ⟶ S) (b : S ⟶ Z) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcDerivedRestrict ((adicTowerInverseImage t).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ⋙
      lisseTowerLocalizationPull t s a b d (n + 1) ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection s d (n + 1)) ≅
      lisseTowerLocalizationPull t s a b d n ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection s d n) :=
  realizationScalar _ _ _ _ _ _ _ _
    (lisseTowerFixedScalarIso t d n (lisseTowerNormalizedScalarSquare t d n))
    (lisseTowerLocalizationFixedScalar s a b d n)

/-- The specified inverse-image coefficient mate, in the direction of semilinear arrows. -/
def lisseTowerInverseImageScalar {X Z : Scheme.{u}} (t : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)) ⋙
        adicTowerPullback t ((pbcAdicRings X d).obj (op (n + 1))) ≅
      adicTowerPullback t ((pbcAdicRings X d).obj (op n)) ⋙
        pbcDerivedRestrict ((adicTowerInverseImage t).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) :=
  show pbcDerivedRestrict _ ⋙ _ ≅ _ ⋙ pbcDerivedRestrict _ from by
  unfold pbcDerivedRestrict
  exact (proEtaleRingRestrictionDerivedPullback t
    ((pbcAdicRings X d).obj (op (n + 1))) ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage t).obj ((pbcAdicRings X d).obj (op (n + 1))))
    ((adicTowerInverseImage t).obj ((pbcAdicRings X d).obj (op n)))
    (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
    ((adicTowerInverseImage t).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)).symm

end AlgebraicGeometry.Scheme
