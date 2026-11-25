/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import
    WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsModel

/-! # Ordinary presentations of the constant comparisons

The constant comparisons of `lisseTower_constant_complex_comparisons` are exact
localizations of ordinary comparisons. This file records the natural constant model
and the ordinary natural isomorphisms represented by all derived comparisons involved.

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03DA
* Sites, Tag 0H7J
* Cohomology on Sites, Tag 06YY
* Derived Categories, Tag 05RU
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

section Model

variable {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
/- The comparison `presentationPullIso`, for the canonical module inverse-image adjunction
`proEtaleRingModuleAdjunction`, which is uniquely normalized on unit sections. -/
private def canonicalPresentationPullAdj {X Z : Scheme.{u}} (g : Z ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {B : Type (u + 1)} [CommRing B]
    (α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of B) ⟶ ((adicLisseForget X).obj R).obj)
    (β : (Functor.const Z.ProEtᵒᵖ).obj (RingCat.of B) ⟶
      ((adicLisseForget Z).obj ((adicTowerInverseImage g).obj R)).obj)
    [Presheaf.IsLocallyInjective (ProEt.topology X) α]
    [Presheaf.IsLocallySurjective (ProEt.topology X) α]
    [Presheaf.IsLocallyInjective (ProEt.topology Z) β]
    [Presheaf.IsLocallySurjective (ProEt.topology Z) β]
    (h : α ≫ Functor.whiskerRight
        ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (proEtaleBaseChange g).op β) :
    constantPresentation α ⋙ proEtaleRingModulePullback g R
        ((adicTowerInverseImage g).obj R) (Iso.refl _) ⊣
      presentationSections β ((proEtaleBaseChange g).obj (⊤_ X.ProEt)) := by
  let V : X.ProEt := ⊤_ X.ProEt
  let hV : IsTerminal V := terminalIsTerminal
  let adj := (presentationAdjunction α V hV).comp
    (proEtaleRingModuleAdjunction g R ((adicTowerInverseImage g).obj R) (Iso.refl _))
  let e : proEtaleRingModuleDirectImage g R
        ((adicTowerInverseImage g).obj R) (Iso.refl _) ⋙ presentationSections α V ≅
      presentationSections β ((proEtaleBaseChange g).obj V) := by
    refine NatIso.ofComponents (fun N ↦ ?_) ?_
    · let r := ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R).hom.app (op V)
      have hr : (β.app (op ((proEtaleBaseChange g).obj V))).hom =
          r.hom.comp (α.app (op V)).hom := by
        exact congrArg RingCat.Hom.hom (congr_app h (op V)).symm
      exact (ModuleCat.restrictScalarsComp'App (α.app (op V)).hom r.hom
        (β.app (op ((proEtaleBaseChange g).obj V))).hom hr
          (N.val.obj (op ((proEtaleBaseChange g).obj V)))).symm
    · intro M N f
      ext x
      rfl
  exact adj.ofNatIsoRight e

/- `presentationPullIso`, for the canonical module inverse-image adjunction. -/
private def canonicalPresentationPullIso {X Z : Scheme.{u}} (g : Z ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {B : Type (u + 1)} [CommRing B]
    (α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of B) ⟶ ((adicLisseForget X).obj R).obj)
    (β : (Functor.const Z.ProEtᵒᵖ).obj (RingCat.of B) ⟶
      ((adicLisseForget Z).obj ((adicTowerInverseImage g).obj R)).obj)
    [Presheaf.IsLocallyInjective (ProEt.topology X) α]
    [Presheaf.IsLocallySurjective (ProEt.topology X) α]
    [Presheaf.IsLocallyInjective (ProEt.topology Z) β]
    [Presheaf.IsLocallySurjective (ProEt.topology Z) β]
    (h : α ≫ Functor.whiskerRight
        ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (proEtaleBaseChange g).op β) :
    constantPresentation α ⋙ proEtaleRingModulePullback g R
        ((adicTowerInverseImage g).obj R) (Iso.refl _) ≅ constantPresentation β :=
  (canonicalPresentationPullAdj g R α β h).leftAdjointUniq (presentationAdjunction β
    ((proEtaleBaseChange g).obj (⊤_ X.ProEt))
    ((terminalIsTerminal : IsTerminal (⊤_ X.ProEt)).isTerminalObj (proEtaleBaseChange g) _))

/- The identity comparison of constant presheaves with identically restricted scalars. -/
private def constantPresheafTransport {C : Type (u + 1)} [Category.{u} C]
    (B : Type (u + 1)) [CommRing B] :
    constantModulePresheaf (C := C) B ≅ constantModulePresheaf (C := C) B ⋙
      CoefficientSheafificationSquare.rawRestriction (RingHom.id B) :=
  NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk
    (fun V ↦ (ModuleCat.restrictScalarsId B).symm.app M)
    (by intros; ext x; rfl)) (by intros; ext V x; rfl)

/- `presentationTransportIso`, with its presheaf comparison named. -/
private def canonicalPresentationTransportIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {B : Type (u + 1)} [CommRing B] {R S : Sheaf J RingCat.{u + 1}}
    (e : R ≅ S)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (h : β = α ≫ e.hom.hom) :
    constantPresentation α ≅ constantPresentation β ⋙ SheafOfModules.restrictScalars e.hom :=
  Functor.isoWhiskerRight (constantPresheafTransport (C := C) B)
      (PresheafOfModules.sheafification α) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (constantModulePresheaf (C := C) B)
      (CoefficientSheafificationSquare.rawIso J (RingHom.id B) e.hom α β
        (by simpa using h)) ≪≫ (Functor.associator _ _ _).symm

/- The identity comparison of the two constant presheaf constructions. -/
private def adicConstantPresheafIso (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    constantModulePresheaf (C := X.ProEt) B ≅
      siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B ⋙
        PresheafOfModules.pushforward₀
          ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
          ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B)) :=
  NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk
    (fun V ↦ (LinearEquiv.refl B M).toModuleIso) (by intro V W f; ext x; rfl))
    (by intro M N f; ext V x; rfl)

/- `sourcePresentationIso`, built from named pieces. -/
private def canonicalSourcePresentationIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    constantPresentation (sourceScalarMap X d n) ≅
      adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1)) ⋙
        pbcRestrict (pbcLevelConstantComparison X d n).inv :=
  canonicalPresentationTransportIso (ProEt.topology X)
      ((adicLisseForget X).mapIso (pbcLevelConstantComparison X d n).symm) (sourceScalarMap X d n)
      (adicLisseConstantUnit X (A ⧸ d.ideal ^ (n + 1)))
      (by
        unfold sourceScalarMap
        rw [Category.assoc]
        change _ = _ ≫ ((adicLisseForget X).map (pbcLevelConstantComparison X d n).hom).hom ≫
          ((adicLisseForget X).map (pbcLevelConstantComparison X d n).inv).hom
        rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp,
          Iso.hom_inv_id, CategoryTheory.Functor.map_id]
        rfl) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (adicConstantPresheafIso X _)
      (PresheafOfModules.sheafification (adicLisseConstantUnit X (A ⧸ d.ideal ^ (n + 1))))) _

/- `ordinaryConstantModel`, for the canonical module inverse-image adjunction. -/
private def canonicalOrdinaryConstantModel {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ⋙
        lisseTowerFixedSheafRealization g d n ≅
      constantAdicQuotientModules X d n ⋙ proEtaleRingModulePullback g
        ((pbcAdicRings X d).obj (op n))
        ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _) := by
  let q := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (constantAdicQuotientMap d.ideal n)
  let C := constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
  let F := lisseTowerFiniteSheafRealization g d n
  let P := proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _)
  let α := sourceScalarMap X d n
  let β := lisseTowerFiniteScalarMap g d n
  let i : C ⋙ sheafCompose (ProEt.topology Z) q ≅
      q ⋙ constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) :=
    constantCommuteCompose (ProEt.topology Z) q
  letI : (ProEt.topology Z).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction (ProEt.topology Z)
      (ModuleCat.forget₂CoinduceAdj _)
  let j := fixedConstantIso (ProEt.topology Z) β
  let k := canonicalPresentationPullIso g ((pbcAdicRings X d).obj (op n)) α β
    (sourceScalarMap_pull g d n)
  exact (Functor.associator C _ F).symm ≪≫ Functor.isoWhiskerRight i F ≪≫
    Functor.associator q _ F ≪≫ Functor.isoWhiskerLeft q j.symm ≪≫
    Functor.isoWhiskerLeft q k.symm ≪≫
    Functor.isoWhiskerLeft q (Functor.isoWhiskerRight (canonicalSourcePresentationIso X d n) P)
        ≪≫
    (Functor.associator q _ P).symm

/- `derivedConstantModel`, for the canonical module inverse-image adjunction. -/
private def canonicalDerivedConstantModel {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    normalizationConstant (ProEt.topology Z) ⋙ lisseTowerFixedRealization g d n ≅
      constantAdicQuotientRealization g d n := by
  unfold constantAdicQuotientRealization
  let C := constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
  let F := lisseTowerFixedSheafRealization g d n
  let P := proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _)
  exact Functor.isoWhiskerLeft C.mapDerivedCategory (lisseTowerFixedRealizationIso g d n).symm
      ≪≫
    Functor.mapDerivedCategoryCompIso C F ≪≫
    Functor.mapDerivedCategoryNatIso (canonicalOrdinaryConstantModel g d n) ≪≫
    (Functor.mapDerivedCategoryCompIso (constantAdicQuotientModules X d n) P).symm


/-- The natural constant model: constants commute with the etale/pro-etale comparison
and with the two inverse images, and the fixed realization of constants is the constant
quotient realization. -/
def lisseTowerConstantModel :
    lisseTowerConstantInput g a b d n ≅ constantAdicQuotientRealization g d n := by
  let B := lisseTowerEtaleRing d n
  unfold lisseTowerConstantInput
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedComparisonConstantIso S B) _ ≪≫
        derivedFixedConstantPullIso a B) _ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedFixedConstantPullIso b B) _ ≪≫
    canonicalDerivedConstantModel g d n

/-- The ordinary natural constant model, before localization. -/
def lisseTowerOrdinaryConstantModel :
    constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) S ⋙
          ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a) ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b ⋙
          lisseTowerFixedSheafRealization g d n ≅
      constantAdicQuotientModules X d n ⋙ proEtaleRingModulePullback g
        ((pbcAdicRings X d).obj (op n))
        ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ProEtale.constantSheafCompComparisonUpperStarIso
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) S) _ ≪≫
        fixedProEtaleConstantIso a (lisseTowerEtaleRing d n)) _ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fixedProEtaleConstantIso b (lisseTowerEtaleRing d n)) _ ≪≫
    canonicalOrdinaryConstantModel g d n

/-- The presentation of the fixed realization by the fixed sheaf realization. -/
def lisseTowerFixedRealizationPresentation :
    DerivedPresentation (lisseTowerFixedRealization g d n)
      (lisseTowerFixedSheafRealization g d n) :=
  (DerivedPresentation.ofMap _).ofIso (lisseTowerFixedRealizationIso g d n)

/-- The presentation of the constant input. -/
def lisseTowerConstantInputPresentation :
    DerivedPresentation (lisseTowerConstantInput g a b d n)
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) S ⋙
          ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a) ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b ⋙
          lisseTowerFixedSheafRealization g d n) :=
  (DerivedPresentation.ofMap _).comp
    (((DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _)).comp
      ((DerivedPresentation.ofMap _).comp (lisseTowerFixedRealizationPresentation g d n)))

/-- The presentation of the constant quotient realization. -/
def constantAdicQuotientRealizationPresentation :
    DerivedPresentation (constantAdicQuotientRealization g d n)
      (constantAdicQuotientModules X d n ⋙ proEtaleRingModulePullback g
        ((pbcAdicRings X d).obj (op n))
        ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _)) :=
  (DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _)

theorem lisseTowerConstantModel_represents :
    DerivedRepresents (lisseTowerConstantInputPresentation g a b d n)
      (constantAdicQuotientRealizationPresentation g d n)
      (lisseTowerConstantModel g a b d n).hom (lisseTowerOrdinaryConstantModel g a b d n).hom := by
  have h1 := derivedRepresents_mapDerivedCategoryCompIso_symm_trans
    (ProEtale.constantSheafCompComparisonUpperStarIso (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
        S)
  have h2 := derivedRepresents_mapDerivedCategoryCompIso_symm_trans
    (fixedProEtaleConstantIso a (lisseTowerEtaleRing d n))
  have h3 := derivedRepresents_mapDerivedCategoryCompIso_symm_trans
    (fixedProEtaleConstantIso b (lisseTowerEtaleRing d n))
  have h4 : DerivedRepresents ((DerivedPresentation.ofMap _).comp
      (lisseTowerFixedRealizationPresentation g d n))
      (constantAdicQuotientRealizationPresentation g d n)
      (canonicalDerivedConstantModel g d n).hom (canonicalOrdinaryConstantModel g d n).hom := by
    have k := ((((derivedRepresents_ofIso (DerivedPresentation.ofMap _)
      (lisseTowerFixedRealizationIso g d n)).inv (τ₀ := Iso.refl _)).whiskerLeft
        (DerivedPresentation.ofMap (constantSheaf (ProEt.topology Z)
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))).comp
      (derivedRepresents_mapDerivedCategoryCompIso_symm_trans
        (canonicalOrdinaryConstantModel g d n))).comp
      (derivedRepresents_mapDerivedCategoryCompIso _ _)
    exact k.congr (by delta canonicalDerivedConstantModel; simp) (by ext; simp)
  have k := ((derivedRepresents_associator_inv _ _ _).comp
    ((((derivedRepresents_associator_inv _ _ _).comp
      ((h1.whiskerRight _).comp h2)).whiskerRight _).comp
    ((derivedRepresents_associator_inv _ _ _).comp
      ((h3.whiskerRight _).comp h4))))
  exact k.congr rfl rfl

end Model


section Paste

variable {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ E : Type*}
  [Category A₀] [Category A₁] [Category B₀] [Category B₁]
  [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category E]
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁]
  [Abelian C₀] [Abelian C₁] [Abelian D₀] [Abelian D₁] [Abelian E]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory B₀]
  [HasDerivedCategory B₁] [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory E]
  {R : DerivedCategory A₀ ⥤ DerivedCategory A₁} {S : DerivedCategory B₀ ⥤ DerivedCategory
      B₁}
  {T : DerivedCategory C₀ ⥤ DerivedCategory C₁}
  {F₀ : DerivedCategory A₀ ⥤ DerivedCategory B₀} {F₁ : DerivedCategory A₁ ⥤
      DerivedCategory B₁}
  {G₀ : DerivedCategory B₀ ⥤ DerivedCategory C₀} {G₁ : DerivedCategory B₁ ⥤
      DerivedCategory C₁}
  {L₀ : DerivedCategory C₀ ⥤ DerivedCategory D₀} {L₁ : DerivedCategory C₁ ⥤
      DerivedCategory D₁}
  {H₀ : DerivedCategory D₀ ⥤ DerivedCategory E} {H₁ : DerivedCategory D₁ ⥤
      DerivedCategory E}
  {r : A₀ ⥤ A₁} {s : B₀ ⥤ B₁} {t : C₀ ⥤ C₁} {f₀ : A₀ ⥤ B₀} {f₁ : A₁
      ⥤ B₁}
  {g₀ : B₀ ⥤ C₀} {g₁ : B₁ ⥤ C₁} {l₀ : C₀ ⥤ D₀} {l₁ : C₁ ⥤ D₁} {h₀
      : D₀ ⥤ E} {h₁ : D₁ ⥤ E}
  [r.Additive] [s.Additive] [t.Additive] [f₀.Additive] [f₁.Additive] [g₀.Additive]
  [g₁.Additive] [l₀.Additive] [l₁.Additive] [h₀.Additive] [h₁.Additive]

/-- The paste of represented squares represents the ordinary paste. -/
theorem derivedRepresents_lisseTowerPasteConstantScalar
    (pR : DerivedPresentation R r) (pS : DerivedPresentation S s)
    (pT : DerivedPresentation T t)
    (pF₀ : DerivedPresentation F₀ f₀) (pF₁ : DerivedPresentation F₁ f₁)
    (pG₀ : DerivedPresentation G₀ g₀) (pG₁ : DerivedPresentation G₁ g₁)
    (pL₀ : DerivedPresentation L₀ l₀) (pL₁ : DerivedPresentation L₁ l₁)
    (pH₀ : DerivedPresentation H₀ h₀) (pH₁ : DerivedPresentation H₁ h₁)
    {e : R ⋙ F₁ ≅ F₀ ⋙ S} {e₀ : r ⋙ f₁ ≅ f₀ ⋙ s}
    {f : S ⋙ G₁ ≅ G₀ ⋙ T} {f' : s ⋙ g₁ ≅ g₀ ⋙ t}
    {h : T ⋙ L₁ ⋙ H₁ ≅ L₀ ⋙ H₀} {h' : t ⋙ l₁ ⋙ h₁ ≅ l₀ ⋙ h₀}
    (he : DerivedRepresents (pR.comp pF₁) (pF₀.comp pS) e.hom e₀.hom)
    (hf : DerivedRepresents (pS.comp pG₁) (pG₀.comp pT) f.hom f'.hom)
    (hh : DerivedRepresents (pT.comp (pL₁.comp pH₁)) (pL₀.comp pH₀) h.hom h'.hom) :
    DerivedRepresents (pR.comp ((pF₁.comp (pG₁.comp pL₁)).comp pH₁))
      ((pF₀.comp (pG₀.comp pL₀)).comp pH₀)
      (lisseTowerPasteConstantScalar R S T F₀ F₁ G₀ G₁ L₀ L₁ H₀ H₁ e f h).hom
      (lisseTowerPasteConstantScalar r s t f₀ f₁ g₀ g₁ l₀ l₁ h₀ h₁ e₀ f' h').hom
          := by
  have k := ((((((derivedRepresents_associator pF₁ (pG₁.comp pL₁) pH₁).comp
      ((derivedRepresents_associator pG₁ pL₁ pH₁).whiskerLeft pF₁)).whiskerLeft pR).comp
    (derivedRepresents_associator_inv pR pF₁ (pG₁.comp (pL₁.comp pH₁)))).comp
    (he.whiskerRight (pG₁.comp (pL₁.comp pH₁)))).comp
    (derivedRepresents_associator pF₀ pS (pG₁.comp (pL₁.comp pH₁)))).comp
    ((((derivedRepresents_associator_inv pS pG₁ (pL₁.comp pH₁)).comp
      (hf.whiskerRight (pL₁.comp pH₁))).comp
      ((derivedRepresents_associator pG₀ pT (pL₁.comp pH₁)).comp
        (hh.whiskerLeft pG₀))).whiskerLeft pF₀) |>.comp
    ((derivedRepresents_associator_inv pG₀ pL₀ pH₀).whiskerLeft pF₀) |>.comp
    (derivedRepresents_associator_inv pF₀ (pG₀.comp pL₀) pH₀)
  exact k.congr (by ext; simp [lisseTowerPasteConstantScalar])
    (by ext; simp [lisseTowerPasteConstantScalar])

end Paste


section Scalar

variable {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

/-- The ordinary comparison/coefficient interchange followed by the pro-etale one. -/
def lisseTowerOrdinaryComparisonCoefficients :
    sheafCompose S.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) ⋙
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) S ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) a) ≅
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) S ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a) ⋙
      sheafCompose (ProEt.topology T)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) :=
  letI := ProEt.isContinuous_overPullback a
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (G := sheafCompose S.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) ⋙
          ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) S)
      (H := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) S ⋙
        sheafCompose (ProEt.topology S)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
      (normalizationPullbackIso S.smallEtaleTopology (toProEt S)
      (ProEt.topology S) (lisseTowerEtaleQuotient d n)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (G := sheafCompose (ProEt.topology S)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) ⋙
          ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) a)
      (H := ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a ⋙
        sheafCompose (ProEt.topology T)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
      (normalizationPullbackIso (ProEt.topology S)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a) (ProEt.topology T)
        (lisseTowerEtaleQuotient d n)) ≪≫
    (Functor.associator _ _ _).symm

theorem localProEtaleComparisonCoefficients_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap _).comp
        ((DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _)))
      (((DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _)).comp
        (DerivedPresentation.ofMap _))
      (localProEtaleComparisonCoefficients a (lisseTowerEtaleQuotient d n)).hom
      (lisseTowerOrdinaryComparisonCoefficients a d n).hom := by
  let := ProEt.isContinuous_overPullback a
  have h1 := derivedRepresents_mapDerivedCategorySquareIso
    (F₁ := sheafCompose S.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
    (F₂ := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) S)
    (G₁ := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) S)
    (G₂ := sheafCompose (ProEt.topology S)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
    (normalizationPullbackIso S.smallEtaleTopology (toProEt S)
      (ProEt.topology S) (lisseTowerEtaleQuotient d n))
  have h2 := derivedRepresents_mapDerivedCategorySquareIso
    (F₁ := sheafCompose (ProEt.topology S)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
    (F₂ := ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) a)
    (G₁ := ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a)
    (G₂ := sheafCompose (ProEt.topology T)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
    (normalizationPullbackIso (ProEt.topology S)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a) (ProEt.topology T)
        (lisseTowerEtaleQuotient d n))
  have k := ((((derivedRepresents_associator_inv _ _ _).comp
    (h1.whiskerRight _)).comp (derivedRepresents_associator _ _ _)).comp
    (h2.whiskerLeft _)).comp (derivedRepresents_associator_inv _ _ _)
  refine k.congr ?_ ?_
  rotate_left
  · simp only [lisseTowerOrdinaryComparisonCoefficients, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Category.assoc]
  unfold localProEtaleComparisonCoefficients localIsomorphismComparisonCoefficients
    localIsomorphismProEtaleCoefficients
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, mapDerivedCategorySquareIso, Category.assoc]


theorem normalizationConstantRestrict_symm_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (lisseTowerEtaleQuotient d n))).comp (DerivedPresentation.ofMap _))
      ((DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap
        (sheafCompose S.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))))
      (normalizationConstantRestrict S.smallEtaleTopology (lisseTowerEtaleQuotient d n)).symm.hom
      (constantCommuteCompose S.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))).symm.hom
            := by
  have h := derivedRepresents_mapDerivedCategorySquareIso
    (constantCommuteCompose S.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
  exact DerivedRepresents.inv (τ := normalizationConstantRestrict S.smallEtaleTopology
      (lisseTowerEtaleQuotient d n)) h

/-- The ordinary fixed scalar square pasted with the coefficient interchange of an
inverse image and the restriction compositor. -/
def lisseTowerOrdinaryPulledScalarIso (c : LisseTowerScalarSquare g d n) :
    sheafCompose (ProEt.topology T)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b ⋙
        lisseTowerFixedSheafRealization g d (n + 1)) ⋙
      pbcRestrict (constantAdicFiniteProjection g d (n + 1)) ≅
    (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b ⋙
        lisseTowerFixedSheafRealization g d n) ⋙
      pbcRestrict (constantAdicFiniteProjection g d n) :=
  letI := ProEt.isContinuous_overPullback b
  Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (G := sheafCompose (ProEt.topology T)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) ⋙
            ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b)
        (H := ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b ⋙
          sheafCompose (ProEt.topology Z)
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
        (normalizationPullbackIso (ProEt.topology T)
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ b) (ProEt.topology Z)
            (lisseTowerEtaleQuotient d n)) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ c ≪≫
      (Functor.associator _ _ _).symm) (pbcRestrict (constantAdicFiniteProjection g d (n + 1)))
          ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pbcRestrictComp (constantAdicFiniteProjection g d (n + 1))
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (constantAdicFiniteProjection g d n)
      (constantAdicFiniteProjection_comp g d (n + 1) n (Nat.le_succ n))) ≪≫
    (Functor.associator (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b)
      (lisseTowerFixedSheafRealization g d n)
      (pbcRestrict (constantAdicFiniteProjection g d n))).symm

theorem lisseTowerFixedScalarIso_represents (c : LisseTowerScalarSquare g d n) :
    DerivedRepresents
      ((DerivedPresentation.ofMap _).comp (lisseTowerFixedRealizationPresentation g d (n + 1)))
      ((lisseTowerFixedRealizationPresentation g d n).comp (DerivedPresentation.ofMap
        (pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))))
      (lisseTowerFixedScalarIso g d n c).hom c.hom := by
  have k := ((((derivedRepresents_ofIso (DerivedPresentation.ofMap _)
      (lisseTowerFixedRealizationIso g d (n + 1))).inv (τ₀ := Iso.refl _)).whiskerLeft
        (DerivedPresentation.ofMap _)).comp
      (derivedRepresents_mapDerivedCategorySquareIso c)).comp
    ((derivedRepresents_ofIso (DerivedPresentation.ofMap _)
      (lisseTowerFixedRealizationIso g d n)).whiskerRight (DerivedPresentation.ofMap
        (pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))))
  refine k.congr ?_ ?_
  · delta lisseTowerFixedScalarIso
    simp only [id, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Category.assoc]
  · ext
    simp

theorem pbcDerivedRestrictComp_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _))
      (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d n)))
      (pbcDerivedRestrictComp (constantAdicFiniteProjection g d (n + 1))
        ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
        (constantAdicFiniteProjection g d n)
        (constantAdicFiniteProjection_comp g d (n + 1) n (Nat.le_succ n))).hom
      (pbcRestrictComp (constantAdicFiniteProjection g d (n + 1))
        ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
        (constantAdicFiniteProjection g d n)
        (constantAdicFiniteProjection_comp g d (n + 1) n (Nat.le_succ n))).hom :=
  derivedRepresents_mapDerivedCategoryCompIso_symm_trans _


theorem localIsomorphismProEtaleCoefficients_represents :
    letI := ProEt.isContinuous_overPullback b
    DerivedRepresents
      ((DerivedPresentation.ofMap (sheafCompose (ProEt.topology T)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))).comp
        (DerivedPresentation.ofMap
          (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b)))
      ((DerivedPresentation.ofMap
          (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b)).comp
        (DerivedPresentation.ofMap (sheafCompose (ProEt.topology Z)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))))
      (localIsomorphismProEtaleCoefficients b (lisseTowerEtaleQuotient d n)).hom
      (normalizationPullbackIso (ProEt.topology T)
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ b) (ProEt.topology Z)
          (lisseTowerEtaleQuotient d n)).hom := by
  let := ProEt.isContinuous_overPullback b
  have h := derivedRepresents_mapDerivedCategorySquareIso
    (F₁ := sheafCompose (ProEt.topology T)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
    (F₂ := ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b)
    (G₁ := ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b)
    (G₂ := sheafCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
    (normalizationPullbackIso (ProEt.topology T)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ b) (ProEt.topology Z)
        (lisseTowerEtaleQuotient d n))
  refine h.congr ?_ rfl
  unfold localIsomorphismProEtaleCoefficients
  simp only [Iso.trans_hom, Iso.symm_hom, mapDerivedCategorySquareIso]

theorem lisseTowerPulledScalarIso_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap _).comp (((DerivedPresentation.ofMap _).comp
        (lisseTowerFixedRealizationPresentation g d (n + 1))).comp
          (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d (n + 1))))))
      (((DerivedPresentation.ofMap _).comp
        (lisseTowerFixedRealizationPresentation g d n)).comp
          (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d n))))
      (lisseTowerPulledScalarIso g b d n).hom
      (lisseTowerOrdinaryPulledScalarIso g b d n (lisseTowerNormalizedScalarSquare g d n)).hom := by
  have hA := localIsomorphismProEtaleCoefficients_represents b d n
  have hB := lisseTowerFixedScalarIso_represents g d n (lisseTowerNormalizedScalarSquare g d n)
  have hK := pbcDerivedRestrictComp_represents g d n
  have k1 := hA.whiskerRight (lisseTowerFixedRealizationPresentation g d (n + 1))
  have k2 := hB.whiskerLeft (DerivedPresentation.ofMap
    (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b))
  have k3 := (derivedRepresents_associator_inv _ _ _).comp (k1.comp
    ((derivedRepresents_associator _ _ _).comp (k2.comp (derivedRepresents_associator_inv _ _ _))))
  have k4 := k3.whiskerRight
    (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d (n + 1))))
  have k5 := hK.whiskerLeft ((DerivedPresentation.ofMap
    (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b)).comp
      (lisseTowerFixedRealizationPresentation g d n))
  have k := ((derivedRepresents_associator_inv _ _ _).comp
    (k4.comp (derivedRepresents_associator _ _ _))).comp k5
  refine k.congr ?_ ?_
  · delta lisseTowerPulledScalarIso
    refine NatTrans.ext (funext fun K ↦ ?_)
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
    erw [Category.comp_id]
    rfl
  · refine NatTrans.ext (funext fun K ↦ ?_)
    simp only [lisseTowerOrdinaryPulledScalarIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Category.assoc]
    erw [Category.comp_id]


/-- The ordinary constant coefficient square, before localization. -/
def lisseTowerOrdinaryConstantScalarIso :=
  lisseTowerPasteConstantScalar
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))
    (sheafCompose S.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
    (sheafCompose (ProEt.topology T)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)))
    (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) S ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) S ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) a)
    (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b ⋙
      lisseTowerFixedSheafRealization g d n)
    (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b ⋙
      lisseTowerFixedSheafRealization g d (n + 1))
    (pbcRestrict (constantAdicFiniteProjection g d n))
    (pbcRestrict (constantAdicFiniteProjection g d (n + 1)))
    (constantCommuteCompose S.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))).symm
    (lisseTowerOrdinaryComparisonCoefficients a d n)
    (lisseTowerOrdinaryPulledScalarIso g b d n (lisseTowerNormalizedScalarSquare g d n))

theorem lisseTowerConstantScalarIso_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap _).comp
        ((lisseTowerConstantInputPresentation g a b d (n + 1)).comp
          (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d (n + 1))))))
      ((lisseTowerConstantInputPresentation g a b d n).comp
          (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d n))))
      (lisseTowerConstantScalarIso g a b d n).hom
      (lisseTowerOrdinaryConstantScalarIso g a b d n).hom := by
  have k := derivedRepresents_lisseTowerPasteConstantScalar
    (DerivedPresentation.ofMap _) (DerivedPresentation.ofMap _) (DerivedPresentation.ofMap _)
    (DerivedPresentation.ofMap _) (DerivedPresentation.ofMap _)
    ((DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _))
    ((DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _))
    ((DerivedPresentation.ofMap _).comp (lisseTowerFixedRealizationPresentation g d n))
    ((DerivedPresentation.ofMap _).comp (lisseTowerFixedRealizationPresentation g d (n + 1)))
    (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d n)))
    (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d (n + 1))))
    (normalizationConstantRestrict_symm_represents (S := S) d n)
    (localProEtaleComparisonCoefficients_represents a d n)
    (lisseTowerPulledScalarIso_represents g b d n)
  refine k.congr ?_ rfl
  delta lisseTowerConstantScalarIso
  rfl

end Scalar


section Right

variable {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso
attribute [local instance] CompletedConstantReduction.constant_additive

/-- The ordinary right square for constants and finite restriction. -/
def constantAdicOrdinaryQuotientRightIso :
    ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk ((d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) ⋙
      (adicLisseConstantModules X (AdicCompletion d.ideal A) ⋙
        proEtaleRingModulePullback g (adicLisseConstantRing X (AdicCompletion d.ideal A))
          ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
          (Iso.refl _)) ≅
    (constantAdicQuotientModules X d n ⋙ proEtaleRingModulePullback g
        ((pbcAdicRings X d).obj (op n))
        ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _)) ⋙
      pbcRestrict (constantAdicFiniteProjection g d n) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constantAdicQuotientComparison X d n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (proEtaleRingRestrictionPullbackInv g
      (adicLisseConstantRing X (AdicCompletion d.ideal A))
      ((pbcAdicRings X d).obj (op n))
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n)))
      ((constantAdicFiniteCone X d).π.app (op n))
      (constantAdicFiniteProjection g d n) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm))) ≪≫
    (Functor.associator _ _ _).symm

/-- The presentation of the constant finite realization. -/
def constantAdicFiniteRealizationPresentation :
    haveI := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).1
    haveI := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).2
    DerivedPresentation (constantAdicFiniteRealization g d)
      (adicLisseConstantModules X (AdicCompletion d.ideal A) ⋙
        proEtaleRingModulePullback g (adicLisseConstantRing X (AdicCompletion d.ideal A))
          ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
          (Iso.refl _)) :=
  haveI := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).1
  haveI := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).2
  (DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _)

theorem constantAdicQuotientRightIso_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap _).comp (constantAdicFiniteRealizationPresentation g d))
      ((constantAdicQuotientRealizationPresentation g d n).comp
        (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d n))))
      (constantAdicQuotientRightIso g d n).hom
      (constantAdicOrdinaryQuotientRightIso g d n).hom := by
  have := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).1
  have := (constantAdicFinite_constant_exact X (AdicCompletion d.ideal A)).2
  have hk := derivedRepresents_mapDerivedCategorySquareIso (constantAdicQuotientComparison X d n)
  have hp := derivedRepresents_mapDerivedCategorySquareIso (asIso
      (proEtaleRingRestrictionPullbackInv g
      (adicLisseConstantRing X (AdicCompletion d.ideal A))
      ((pbcAdicRings X d).obj (op n))
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X (AdicCompletion d.ideal A)))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n)))
      ((constantAdicFiniteCone X d).π.app (op n))
      (constantAdicFiniteProjection g d n) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm))).symm
  have hpi := DerivedRepresents.inv (τ := mapDerivedCategorySquareIso _) hp
  have k := (derivedRepresents_associator_inv _ _ _).comp ((hk.whiskerRight _).comp
    ((derivedRepresents_associator _ _ _).comp ((hpi.whiskerLeft _).comp
      (derivedRepresents_associator_inv _ _ _))))
  refine k.congr ?_ ?_
  · delta constantAdicQuotientRightIso constantAdicQuotientPullComparison
      proEtaleRingRestrictionDerivedPullback
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Category.assoc, mapDerivedCategorySquareIso, Iso.trans_inv,
      Iso.symm_inv]
  · simp only [constantAdicOrdinaryQuotientRightIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_inv]


/-- The ordinary constant model, transported to completion coefficients. -/
def lisseTowerOrdinaryConstantModelIso :=
  Functor.isoWhiskerRight (lisseTowerOrdinaryConstantModel g a b d n)
      (pbcRestrict (constantAdicFiniteProjection g d n)) ≪≫
    (constantAdicOrdinaryQuotientRightIso g d n).symm

theorem lisseTowerConstantModelIso_represents :
    DerivedRepresents
      ((lisseTowerConstantInputPresentation g a b d n).comp
          (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d n))))
      ((DerivedPresentation.ofMap _).comp (constantAdicFiniteRealizationPresentation g d))
      (lisseTowerConstantModelIso g a b d n (lisseTowerConstantModel g a b d n)).hom
      (lisseTowerOrdinaryConstantModelIso g a b d n).hom := by
  have k := ((lisseTowerConstantModel_represents g a b d n).whiskerRight
    (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection g d n)))).comp
    (DerivedRepresents.inv (τ := constantAdicQuotientRightIso g d n)
      (τ₀ := constantAdicOrdinaryQuotientRightIso g d n)
      (constantAdicQuotientRightIso_represents g d n))
  refine k.congr ?_ ?_
  · simp only [lisseTowerConstantModelIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom]
    rfl
  · simp only [lisseTowerOrdinaryConstantModelIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom]

/-- The ordinary composition of restrictions along consecutive quotients. -/
def lisseTowerOrdinaryAlgebraRestrictIso :=
  (ModuleCat.restrictScalarsComp'.{u + 1}
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 2)))
      (lisseTowerEtaleQuotient d n)
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk _).symm).symm

theorem lisseTowerAlgebraRestrictIso_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (lisseTowerEtaleQuotient d n))).comp (DerivedPresentation.ofMap _))
      (DerivedPresentation.ofMap _)
      (lisseTowerAlgebraRestrictIso d n).hom (lisseTowerOrdinaryAlgebraRestrictIso d n).hom := by
  have k := (derivedRepresents_mapDerivedCategoryCompIso_inv _ _).comp
    (DerivedRepresents.inv (τ := mapDerivedCategoryNatIso _)
      (derivedRepresents_mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{u + 1}
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 2)))
      (lisseTowerEtaleQuotient d n)
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk _).symm)))
  refine k.congr ?_ ?_
  · simp only [lisseTowerAlgebraRestrictIso, Iso.trans_hom, Iso.symm_hom]
  · simp only [lisseTowerOrdinaryAlgebraRestrictIso, Iso.symm_hom, Category.id_comp]

end Right



end AlgebraicGeometry.Scheme
