/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence

/-!
# Canonical compact-support composition on the etale-origin class

Source: blueprint proposition-composition-base-change-rf-shriek--1, construction and coherence
paragraphs; Stacks Project, Tags 0F7J and 0F7K (blueprint:
proposition-composition-base-change-rf-shriek--1). The comparison is transported from the specified
etale compositor. Full faithfulness makes it natural for all ambient morphisms, independently of
retained witnesses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private lemma preimage_whiskerLeft {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (Φ : C ⥤ D) [Φ.IsEquivalence] {F G : D ⥤ E}
    (e : Φ ⋙ F ≅ Φ ⋙ G) :
    Functor.whiskerLeft Φ
      ((Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
        (X := F) (Y := G) e).hom = e.hom :=
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).map_preimage
    (X := F) (Y := G) e.hom

private lemma preimage_whiskerBoth {C D E B : Type*} [Category* C] [Category* D]
    [Category* E] [Category* B] (Φ : C ⥤ D) [Φ.IsEquivalence] (I : E ⥤ B)
    (H : I.FullyFaithful) {F G : D ⥤ E} (e : Φ ⋙ (F ⋙ I) ≅ Φ ⋙ (G ⋙ I)) :
    Functor.whiskerLeft Φ (Functor.whiskerRight
      ((H.whiskeringRight D).preimageIso (X := F) (Y := G)
        ((Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
          (X := F ⋙ I) (Y := G ⋙ I) e)).hom I) = e.hom := by
  have h := (H.whiskeringRight D).map_preimage (X := F) (Y := G)
    (((Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
      (X := F ⋙ I) (Y := G ⋙ I) e).hom)
  change Functor.whiskerRight _ I = _ at h
  erw [h]
  exact preimage_whiskerLeft Φ (F := F ⋙ I) (G := G ⋙ I) e

private lemma transported_unit_right {C D E B : Type*} [Category* C] [Category* D]
    [Category* E] [Category* B] (Φ : C ⥤ D) (Ψ : E ⥤ B)
    {P : E ⥤ E} {Q : B ⥤ B} {F F' : C ⥤ E} {G G' : D ⥤ B}
    (t₀ : Ψ ⋙ Q ≅ P ⋙ Ψ) (t : Φ ⋙ G ≅ F ⋙ Ψ) (t' : Φ ⋙ G' ≅ F' ⋙ Ψ)
    (i : P ≅ 𝟭 _) (j : Q ≅ 𝟭 _) (e : F ⋙ P ≅ F') (o : G ⋙ Q ≅ G')
    (r : F ≅ F') (s : G ≅ G')
    (hc : Functor.whiskerLeft Φ o.hom ≫ t'.hom =
      Functor.whiskerRight t.hom Q ≫ Functor.whiskerLeft F t₀.hom ≫
        Functor.whiskerRight e.hom Ψ)
    (hi : Functor.whiskerLeft Ψ j.hom = t₀.hom ≫ Functor.whiskerRight i.hom Ψ)
    (ht : Functor.whiskerLeft Φ s.hom ≫ t'.hom =
      t.hom ≫ Functor.whiskerRight r.hom Ψ)
    (he : e.hom = Functor.whiskerLeft F i.hom ≫ (Functor.rightUnitor F).hom ≫ r.hom) :
    Functor.whiskerLeft Φ o.hom = Functor.whiskerLeft Φ
      (Functor.whiskerLeft G j.hom ≫ (Functor.rightUnitor G).hom ≫ s.hom) := by
  apply NatTrans.ext
  funext L
  apply (cancel_mono (t'.hom.app L)).1
  have hc' := congr_app hc L
  have hi' := congr_app hi (F.obj L)
  have ht' := congr_app ht L
  have he' := congr_app he L
  have hn := j.hom.naturality (t.hom.app L)
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.id_map] at hc' hi' ht' he' hn ⊢
  rw [hc', he']
  simp only [Functor.map_comp, Functor.rightUnitor_hom_app, Category.assoc]
  rw [← reassoc_of% hi', reassoc_of% hn, ht']
  erw [Ψ.map_id, Category.id_comp, Category.id_comp]

private lemma transported_associativity
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₀] [Category* D₁] [Category* D₂] [Category* D₃]
    (Φ₀ : C₀ ⥤ D₀) (Φ₁ : C₁ ⥤ D₁) (Φ₂ : C₂ ⥤ D₂) (Φ₃ : C₃ ⥤ D₃)
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃}
    {FG : C₀ ⥤ C₂} {GH : C₁ ⥤ C₃} {L R : C₀ ⥤ C₃}
    {f : D₀ ⥤ D₁} {g : D₁ ⥤ D₂} {h : D₂ ⥤ D₃}
    {fg : D₀ ⥤ D₂} {gh : D₁ ⥤ D₃} {l r : D₀ ⥤ D₃}
    (tF : Φ₀ ⋙ f ≅ F ⋙ Φ₁) (tG : Φ₁ ⋙ g ≅ G ⋙ Φ₂)
    (tH : Φ₂ ⋙ h ≅ H ⋙ Φ₃) (tFG : Φ₀ ⋙ fg ≅ FG ⋙ Φ₂)
    (tGH : Φ₁ ⋙ gh ≅ GH ⋙ Φ₃) (tL : Φ₀ ⋙ l ≅ L ⋙ Φ₃)
    (tR : Φ₀ ⋙ r ≅ R ⋙ Φ₃)
    (e₁ : F ⋙ G ≅ FG) (e₂ : FG ⋙ H ≅ L) (e₃ : G ⋙ H ≅ GH)
    (e₄ : F ⋙ GH ≅ R) (e₅ : L ≅ R)
    (o₁ : f ⋙ g ≅ fg) (o₂ : fg ⋙ h ≅ l) (o₃ : g ⋙ h ≅ gh)
    (o₄ : f ⋙ gh ≅ r) (o₅ : l ≅ r)
    (hc₁ : Functor.whiskerLeft Φ₀ o₁.hom ≫ tFG.hom =
      Functor.whiskerRight tF.hom g ≫ Functor.whiskerLeft F tG.hom ≫
        Functor.whiskerRight e₁.hom Φ₂)
    (hc₂ : Functor.whiskerLeft Φ₀ o₂.hom ≫ tL.hom =
      Functor.whiskerRight tFG.hom h ≫ Functor.whiskerLeft FG tH.hom ≫
        Functor.whiskerRight e₂.hom Φ₃)
    (hc₃ : Functor.whiskerLeft Φ₁ o₃.hom ≫ tGH.hom =
      Functor.whiskerRight tG.hom h ≫ Functor.whiskerLeft G tH.hom ≫
        Functor.whiskerRight e₃.hom Φ₃)
    (hc₄ : Functor.whiskerLeft Φ₀ o₄.hom ≫ tR.hom =
      Functor.whiskerRight tF.hom gh ≫ Functor.whiskerLeft F tGH.hom ≫
        Functor.whiskerRight e₄.hom Φ₃)
    (ht : Functor.whiskerLeft Φ₀ o₅.hom ≫ tR.hom =
      tL.hom ≫ Functor.whiskerRight e₅.hom Φ₃)
    (he : Functor.whiskerRight e₁.hom H ≫ e₂.hom ≫ e₅.hom =
      (Functor.associator F G H).hom ≫ Functor.whiskerLeft F e₃.hom ≫ e₄.hom) :
    Functor.whiskerLeft Φ₀ (Functor.whiskerRight o₁.hom h ≫ o₂.hom ≫ o₅.hom) =
      Functor.whiskerLeft Φ₀
        ((Functor.associator f g h).hom ≫ Functor.whiskerLeft f o₃.hom ≫ o₄.hom) := by
  apply NatTrans.ext
  funext K
  apply (cancel_mono (tR.hom.app K)).1
  have ht' := congr_app ht K
  have hc₁' := congr_app hc₁ K
  have hc₂' := congr_app hc₂ K
  have hc₃' := congr_app hc₃ (F.obj K)
  have hc₄' := congr_app hc₄ K
  have he' := congr_app he K
  have hn₁ := tH.hom.naturality (e₁.hom.app K)
  have hn₂ := o₃.hom.naturality (tF.hom.app K)
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_map] at ht' hc₁' hc₂' hc₃' hc₄' he' hn₁ hn₂ ⊢
  simp only [Functor.associator_hom_app, Category.id_comp, Category.assoc] at he' ⊢
  rw [ht', reassoc_of% hc₂', ← Functor.map_comp_assoc, hc₁']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn₁, ← Φ₃.map_comp, ← Φ₃.map_comp, he']
  simp only [Functor.map_comp]
  rw [← reassoc_of% hc₃', reassoc_of% hn₂, ← hc₄']

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [QuasiCompact f] [QuasiCompact g]

/-- Compact support restricted to the full bounded-below etale-origin class.
Source: blueprint proposition-composition-base-change-rf-shriek--1, first paragraph
(blueprint: proposition-composition-base-change-rf-shriek--1). -/
def originCompactSupport :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory ⥤
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).FullSubcategory :=
  ObjectProperty.lift _
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (fun K ↦ K.property.rightDerivedLowerShriek_obj f)

/-- The ordered etale model of the compositor, using the actual compact-support
comparison, bounded-below compatibility, and the canonical etale compositor.
Source: blueprint proposition-composition-base-change-rf-shriek--1, proof steps 2 and 7
(blueprint: proposition-composition-base-change-rf-shriek--1). -/
def originCompositionModel :
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  Functor.isoWhiskerRight (compactSupportSiteComparison A (HasCompactification.compactification f))
      (rightDerivedLowerShriek _ g) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).symm
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        rightDerivedLowerShriek _ g) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus _ f)
      (compactSupportSiteComparison A (HasCompactification.compactification g)) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus _ f)
      (Functor.isoWhiskerRight
        (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).symm
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory) ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusCompIso A f g)
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g))
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory ≪≫
    (compactSupportSiteComparison A (HasCompactification.compactification (f ≫ g))).symm

/-- Descend the specified model along the canonical etale-origin equivalence.
This preimage is unique, rather than an arbitrary choice of a natural isomorphism.
Source: blueprint proposition-composition-base-change-rf-shriek--1, witness conjugation in proof
step 2 (blueprint: proposition-composition-base-change-rf-shriek--1). -/
def originCompositionAmbient :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (originCompositionModel A f g)

/-- The canonical natural isomorphism alpha on the full origin class. Its homs are
all ambient derived morphisms, so changing or forgetting witnesses does not affect it.
Source: blueprint proposition-composition-base-change-rf-shriek--1, displayed isomorphism
(blueprint: proposition-composition-base-change-rf-shriek--1). -/
def originComposition :
    originCompactSupport A f ⋙ originCompactSupport A g ≅ originCompactSupport A (f ≫ g) :=
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  (H.whiskeringRight _).preimageIso (originCompositionAmbient A f g)

/-- Canonical identity comparison, transported from the ordinary etale identity.
Source: blueprint proposition-composition-base-change-rf-shriek--1, identity convention
(blueprint: proposition-composition-base-change-rf-shriek--1). -/
def originCompactSupportId (T : Scheme.{u}) :
    originCompactSupport A (𝟙 T) ≅ 𝟭 _ :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let model := compactSupportSiteComparison A (HasCompactification.compactification (𝟙 T)) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 T)).symm ν ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusId A T)
      (DerivedCategory.Plus.ι ⋙ ν)
  let ambient : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι :=
    (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).fullyFaithfulι
  (H.whiskeringRight _).preimageIso ambient

/-- Equality transport for the chosen compact-support functors.
Source: blueprint proposition-composition-base-change-rf-shriek--1, coherent identifications
(blueprint: proposition-composition-base-change-rf-shriek--1). -/
def originCompactSupportCongr {f' : X ⟶ Y} [HasCompactification f'] (h : f = f') :
    originCompactSupport A f ≅ originCompactSupport A f' :=
  h ▸ Iso.refl _

private lemma originComposition_model :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
      (Functor.whiskerRight (originComposition A f g).hom
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι) =
      (originCompositionModel A f g).hom := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  exact preimage_whiskerBoth Φ _ H
    (F := originCompactSupport A f ⋙ originCompactSupport A g)
    (G := originCompactSupport A (f ≫ g)) (originCompositionModel A f g)

private def originComparison :
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
        originCompactSupport A f ≅
      Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f ⋙
        comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y :=
  let e := compactSupportSiteComparison A (HasCompactification.compactification f) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).symm
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  NatIso.ofComponents (fun L ↦ ObjectProperty.isoMk _ (e.app L))
    (fun t ↦ (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).hom_ext
      (e.hom.naturality t))

-- Keep the large chosen comparisons folded while checking the coherence squares.
attribute [local irreducible] originComparison originComposition

private lemma originComparison_comp :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
        (originComposition A f g).hom ≫ (originComparison A (f ≫ g)).hom =
      Functor.whiskerRight (originComparison A f).hom (originCompactSupport A g) ≫
        Functor.whiskerLeft (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
          (originComparison A g).hom ≫
        Functor.whiskerRight (Etale.rightDerivedLowerShriekPlusCompIso A f g).hom
          (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Z) := by
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  apply (H.whiskeringRight
    (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))).map_injective
  change Functor.whiskerRight
    (Functor.whiskerLeft _ (originComposition A f g).hom ≫ _) _ = _
  rw [Functor.whiskerRight_comp]
  change Functor.whiskerLeft
      (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
      (Functor.whiskerRight (originComposition A f g).hom
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι) ≫ _ = _
  rw [originComposition_model]
  ext K
  simp [originComparison, originCompositionModel, originCompactSupport,
    comparisonUpperStarPlusEtaleOrigin, Category.assoc, ← Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc]

omit [QuasiCompact f] in
private lemma originComparison_congr {f' : X ⟶ Y} [HasCompactification f'] (w : f = f') :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
        (originCompactSupportCongr A f w).hom ≫ (originComparison A f').hom =
      (originComparison A f).hom ≫
        Functor.whiskerRight (Etale.rightDerivedLowerShriekPlusCongr A w).hom
          (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y) := by
  subst f'
  have h : Etale.rightDerivedLowerShriekPlusCongr A (rfl : f = f) = Iso.refl _ := rfl
  simp only [originCompactSupportCongr, h, Iso.refl_hom, Functor.whiskerLeft_id',
    Functor.whiskerRight_id', Category.comp_id, Category.id_comp]

private lemma originComparison_id (T : Scheme.{u}) :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T)
        (originCompactSupportId A T).hom =
      (originComparison A (𝟙 T)).hom ≫
        Functor.whiskerRight (Etale.rightDerivedLowerShriekPlusId A T).hom
          (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T) := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let model := compactSupportSiteComparison A (HasCompactification.compactification (𝟙 T)) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 T)).symm ν ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusId A T)
      (DerivedCategory.Plus.ι ⋙ ν)
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).fullyFaithfulι
  have h := preimage_whiskerBoth Φ _ H
    (F := originCompactSupport A (𝟙 T)) (G := 𝟭 _) model
  apply (H.whiskeringRight
    (DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))).map_injective
  change Functor.whiskerLeft Φ
    (Functor.whiskerRight (originCompactSupportId A T).hom
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι) = _
  erw [h]
  ext L
  simp [model, ν, originComparison, comparisonUpperStarPlusEtaleOrigin, Category.assoc]

attribute [local irreducible] originCompactSupportId
  originCompactSupportCongr originCompactSupport comparisonUpperStarPlusEtaleOrigin
  Etale.rightDerivedLowerShriekPlusCompIso Etale.rightDerivedLowerShriekPlus
  CompactSupportFormalism.lowerShriekId CompactSupportFormalism.lowerShriekCongr

/-- The canonical compositor is the identity when its second morphism is an identity.
Source: blueprint proposition-composition-base-change-rf-shriek--1, unit clause
(blueprint: proposition-composition-base-change-rf-shriek--1).
Proof: expand the model after precomposition with the comparison equivalence. Cancel
adjacent comparisons, apply the etale right-unit equation, and reflect equality by
full faithfulness. This is independent of any choice of etale-origin witness. -/
theorem originComposition_id_right [HasCompactification (f ≫ 𝟙 Y)] :
    (originComposition A f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (originCompactSupportId A Y).hom ≫
        (Functor.rightUnitor _).hom ≫
          (originCompactSupportCongr A f (Category.comp_id f).symm).hom := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  apply (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).map_injective
  change Functor.whiskerLeft Φ _ = Functor.whiskerLeft Φ _
  exact transported_unit_right Φ
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y)
    (originComparison A (𝟙 Y)) (originComparison A f) (originComparison A (f ≫ 𝟙 Y))
    (Etale.rightDerivedLowerShriekPlusId A Y) (originCompactSupportId A Y)
    (Etale.rightDerivedLowerShriekPlusCompIso A f (𝟙 Y)) (originComposition A f (𝟙 Y))
    (Etale.rightDerivedLowerShriekPlusCongr A (Category.comp_id f).symm)
    (originCompactSupportCongr A f (Category.comp_id f).symm)
    (originComparison_comp A f (𝟙 Y)) (originComparison_id A Y)
    (originComparison_congr A f (Category.comp_id f).symm)
    (Etale.rightDerivedLowerShriekPlusCompIso_id_right A f)

/-- Associativity with the specified associator and equality transport.
Source: blueprint proposition-composition-base-change-rf-shriek--1, associativity clause
(blueprint: proposition-composition-base-change-rf-shriek--1).
Proof: expand every model after the fully faithful etale-origin equivalence.
Comparison composition coherence cancels the intermediate site comparisons. Both
remaining expressions are the etale associativity equation, conjugated by the same
end comparisons. Reflect the equality using full faithfulness. -/
theorem originComposition_assoc {T : Scheme.{u}} (h : Z ⟶ T)
    [HasCompactification h] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)]
    [QuasiCompact h] :
    Functor.whiskerRight (originComposition A f g).hom (originCompactSupport A h) ≫
        (originComposition A (f ≫ g) h).hom ≫
        (originCompactSupportCongr A ((f ≫ g) ≫ h) (Category.assoc f g h)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (originCompactSupport A f) (originComposition A g h).hom ≫
          (originComposition A f (g ≫ h)).hom := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  apply (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).map_injective
  change Functor.whiskerLeft Φ _ = Functor.whiskerLeft Φ _
  exact transported_associativity Φ
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y)
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Z)
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T)
    (originComparison A f) (originComparison A g) (originComparison A h)
    (originComparison A (f ≫ g)) (originComparison A (g ≫ h))
    (originComparison A ((f ≫ g) ≫ h)) (originComparison A (f ≫ g ≫ h))
    (Etale.rightDerivedLowerShriekPlusCompIso A f g)
    (Etale.rightDerivedLowerShriekPlusCompIso A (f ≫ g) h)
    (Etale.rightDerivedLowerShriekPlusCompIso A g h)
    (Etale.rightDerivedLowerShriekPlusCompIso A f (g ≫ h))
    (Etale.rightDerivedLowerShriekPlusCongr A (Category.assoc f g h))
    (originComposition A f g) (originComposition A (f ≫ g) h)
    (originComposition A g h) (originComposition A f (g ≫ h))
    (originCompactSupportCongr A ((f ≫ g) ≫ h) (Category.assoc f g h))
    (originComparison_comp A f g) (originComparison_comp A (f ≫ g) h)
    (originComparison_comp A g h) (originComparison_comp A f (g ≫ h))
    (originComparison_congr A ((f ≫ g) ≫ h) (Category.assoc f g h))
    (Etale.rightDerivedLowerShriekPlusCompIso_assoc A f g h)

end AlgebraicGeometry.ProEtale
