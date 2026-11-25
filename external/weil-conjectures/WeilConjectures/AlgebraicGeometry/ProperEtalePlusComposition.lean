/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupportsRaw
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Proper forget-supports composition on the bounded-below etale category

Source: the ordered exterior-product and comparison paragraphs of
sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory DerivedCategory.TStructure.t
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar upperStar openImmersionLowerShriek

private theorem ordinary_comp_eq (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f)
      (lowerStar (ModuleCat.{u + 1} A) g)
      (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom =
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).hom := by
  let B := ModuleCat.{u + 1} A
  have := (upperStarLowerStarAdjunction B f).preservesKInjectiveComplexes
  rw [rightDerivedLowerStarCompIsoOfComp, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_leftDerivedUpperStarComp_hom]
  exact Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction B f) (upperStarLowerStarAdjunction B g)
    (upperStarLowerStarAdjunction B (f ≫ g)) (lowerStarComp B f g)
    (upperStarComp B f g (f ≫ g) rfl)
    (by exact (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp B f g (f ≫ g) rfl)).symm)


/-- Naturality of the componentwise lift to a full subcategory. -/
theorem fullSubcategoryLift_naturality
    {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ P.FullSubcategory}
    (e : F ⋙ P.ι ≅ G ⋙ P.ι) {K L : C} (f : K ⟶ L) :
    F.map f ≫ (ObjectProperty.isoMk P (e.app L)).hom =
      (ObjectProperty.isoMk P (e.app K)).hom ≫ G.map f := by
  apply P.ι.map_injective
  exact e.hom.naturality f

/-- Lift the components of an ambient comparison to the full subcategory. -/
@[irreducible]
def fullSubcategoryLiftIso
    {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ P.FullSubcategory}
    (e : F ⋙ P.ι ≅ G ⋙ P.ι) : F ≅ G :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk P (e.app K))
    (fullSubcategoryLift_naturality P e)

/-- The lifted map has the prescribed ambient component. -/
theorem fullSubcategoryLiftIso_hom
    {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ P.FullSubcategory}
    (e : F ⋙ P.ι ≅ G ⋙ P.ι) (K : C) :
    P.ι.map ((fullSubcategoryLiftIso P e).hom.app K) = e.hom.app K := by
  unfold fullSubcategoryLiftIso
  rfl

/-- Inclusion cancels the final comparison in the lifted conjugate. -/
theorem fullSubcategoryLiftIso_conjugate
    {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ P.FullSubcategory} {U V : C ⥤ D}
    (a : F ⋙ P.ι ≅ U) (b : U ≅ V) (c : G ⋙ P.ι ≅ V) (K : C) :
    P.ι.map ((fullSubcategoryLiftIso P (a ≪≫ b ≪≫ c.symm)).hom.app K) ≫
      c.hom.app K = a.hom.app K ≫ b.hom.app K := by
  rw [fullSubcategoryLiftIso_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

/-- The unique bounded-below restriction of the canonical proper forget-supports iso. -/
def properLowerShriekPlusIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus :=
  fullSubcategoryLiftIso DerivedCategory.TStructure.t.plus
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f) ≪≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.symm)

private theorem proper_plus_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((properLowerShriekPlusIso A f).hom.app K) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app K =
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom.app K ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
  unfold properLowerShriekPlusIso
  exact fullSubcategoryLiftIso_conjugate DerivedCategory.TStructure.t.plus
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f)
    (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f))
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility K

/-- The inclusion equation as a natural transformation, before taking components.
(blueprint: lem-pur-proper-etale-plus-composition). -/
theorem properLowerShriekPlusIso_hom_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Functor.whiskerRight (properLowerShriekPlusIso A f).hom DerivedCategory.Plus.ι ≫
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom =
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom := by
  apply NatTrans.ext
  funext K
  exact proper_plus_hom A f K

private theorem right_derived_comp_prime_plus_congr
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (d : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ H.rightDerivedFunctor)
    (h : (Functor.rightDerivedFunctorCompIso' F G e).hom = d.hom)
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
        ((Functor.rightDerivedFunctorPlusCompIso' F G e).hom.app K) ≫
      H.rightDerivedFunctorPlusCompatibility.hom.app K =
    G.rightDerivedFunctorPlusCompatibility.hom.app (F.rightDerivedFunctorPlus.obj K) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      d.hom.app (DerivedCategory.Plus.ι.obj K) := by
  rw [← h]
  exact right_derived_comp_prime_plus F G e K

private theorem restriction_proper_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (I₀ : C₀ ⥤ D₀) (I₁ : C₁ ⥤ D₁) (I₂ : C₂ ⥤ D₂) [I₂.Faithful]
    (F F' : C₀ ⥤ C₁) (G G' : C₁ ⥤ C₂) (H H' : C₀ ⥤ C₂)
    (U U' : D₀ ⥤ D₁) (V V' : D₁ ⥤ D₂) (W W' : D₀ ⥤ D₂)
    (aF : F ⋙ I₁ ≅ I₀ ⋙ U) (aG : G ⋙ I₂ ≅ I₁ ⋙ V)
    (aH : H ⋙ I₂ ≅ I₀ ⋙ W)
    (dF : F' ⋙ I₁ ≅ I₀ ⋙ U') (dG : G' ⋙ I₂ ≅ I₁ ⋙ V')
    (dH : H' ⋙ I₂ ≅ I₀ ⋙ W')
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H')
    (eU : U ≅ U') (eV : V ≅ V') (eW : W ≅ W')
    (α : F ⋙ G ≅ H) (α₀ : U ⋙ V ≅ W)
    (c : F' ⋙ G' ≅ H') (c₀ : U' ⋙ V' ≅ W')
    (hF : ∀ K, I₁.map (eF.hom.app K) ≫ dF.hom.app K =
      aF.hom.app K ≫ eU.hom.app (I₀.obj K))
    (hG : ∀ K, I₂.map (eG.hom.app K) ≫ dG.hom.app K =
      aG.hom.app K ≫ eV.hom.app (I₁.obj K))
    (hH : ∀ K, I₂.map (eH.hom.app K) ≫ dH.hom.app K =
      aH.hom.app K ≫ eW.hom.app (I₀.obj K))
    (hα : ∀ K, I₂.map (α.hom.app K) ≫ aH.hom.app K =
      aG.hom.app (F.obj K) ≫ V.map (aF.hom.app K) ≫ α₀.hom.app (I₀.obj K))
    (hc : ∀ K, I₂.map (c.hom.app K) ≫ dH.hom.app K =
      dG.hom.app (F'.obj K) ≫ V'.map (dF.hom.app K) ≫ c₀.hom.app (I₀.obj K))
    (hn : α₀.hom ≫ eW.hom =
      Functor.whiskerRight eU.hom V ≫ Functor.whiskerLeft U' eV.hom ≫ c₀.hom) (K : C₀) :
    α.hom.app K ≫ eH.hom.app K =
      G.map (eF.hom.app K) ≫ eG.hom.app (F'.obj K) ≫ c.hom.app K := by
  apply I₂.map_injective
  apply (cancel_mono (dH.hom.app K)).1
  simp only [Functor.map_comp, Category.assoc]
  have hnK := congr_app hn (I₀.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hnK
  rw [hH, reassoc_of% hα, hnK]
  rw [hc]
  rw [reassoc_of% hG]
  have ha := aG.hom.naturality (eF.hom.app K)
  simp only [Functor.comp_map] at ha
  rw [reassoc_of% ha]
  have he := eV.hom.naturality (dF.hom.app K)
  rw [← reassoc_of% he]
  conv_rhs => rw [← V.map_comp_assoc]
  rw [hF]
  simp only [Functor.map_comp, Category.assoc]

private theorem ordinary_plus_compat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((ProEtale.etaleComparisonDirectImageCompIso A f g).hom.app K) ≫
      (lowerStar (ModuleCat.{u + 1} A) (f ≫ g)).rightDerivedFunctorPlusCompatibility.hom.app K =
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility.hom.app
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ≫
      (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
  exact right_derived_comp_prime_plus_congr (lowerStar (ModuleCat.{u + 1} A) f)
    (lowerStar (ModuleCat.{u + 1} A) g) (lowerStarComp (ModuleCat.{u + 1} A) f g)
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl)
    (ordinary_comp_eq A f g) K

/-- `unboundedEtaleCompactSupport_composition_plus`, with the unbounded compositor written as
the inverse of `rightDerivedLowerShriekCompIso` (the two agree by definition). -/
private theorem composition_plus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusCompIso A f g).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g)).hom.app K =
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).hom.app
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom.app K) ≫
      (rightDerivedLowerShriekCompIso A f g).inv.app (DerivedCategory.Plus.ι.obj K) := by
  have e : (unboundedEtaleLowerShriekCompIso A f g).hom =
      (rightDerivedLowerShriekCompIso A f g).inv := by
    apply NatTrans.ext
    funext M
    simp only [unboundedEtaleLowerShriekCompIso, rightDerivedLowerShriekCompIso,
      Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Category.assoc]
    rfl
  rw [← e]
  exact unboundedEtaleCompactSupport_composition_plus A f g K

attribute [local irreducible] rightDerivedLowerShriek rightDerivedLowerShriekPlus
  rightDerivedLowerShriekPlusCompatibility rightDerivedLowerShriekIsoRightDerivedLowerStar
  rightDerivedLowerShriekPlusCompIso rightDerivedLowerShriekCompIso properLowerShriekPlusIso
  ProEtale.etaleComparisonDirectImageCompIso rightDerivedLowerStarCompIsoOfComp

private theorem proper_native_ambient (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g]
    (E : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekCompIso A f g).inv.app E ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) (f ≫ g)).hom.app E =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) f).hom.app E) ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) g).hom.app
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
            E) ≫
      (rightDerivedLowerStarCompIsoOfComp
        (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).hom.app E := by
  exact properShriekComp_comp_forgetSupports_raw A f g E

private theorem proper_native_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] :
    (rightDerivedLowerShriekCompIso A f g).inv ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) (f ≫ g)).hom =
      Functor.whiskerRight
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) ≫
        Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) g).hom ≫
        (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).hom := by
  apply NatTrans.ext
  funext E
  exact proper_native_ambient A f g E

/-- Proper forget-supports composition on the bounded-below etale category.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered composition and comparison;
parent proof Step 2 (blueprint: lem-pur-proper-etale-plus-composition).

Proof: The inclusion of D+ is fully faithful. Its inclusion equation identifies the
constructed proper comparison with the published unbounded comparison after the two
inclusion isomorphisms.
Apply this inclusion and cancel the ordinary composite inclusion map. The compact-support
restriction equation and properShriekComp_comp_forgetSupports_raw give the native ordinary
compositor. Its adjunction-defined and generic derived versions agree by the inverse-image
composition mate formula. Compatibility of generic composition with D+, followed by naturality
of the inclusion and proper comparisons, gives the other side. Cancel the final isomorphism. -/
theorem properLowerShriekPlusIso_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (rightDerivedLowerShriekPlusCompIso A f g).hom.app K ≫
      (properLowerShriekPlusIso A (f ≫ g)).hom.app K =
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g).map
        ((properLowerShriekPlusIso A f).hom.app K) ≫
      (properLowerShriekPlusIso A g).hom.app
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ≫
      (ProEtale.etaleComparisonDirectImageCompIso A f g).hom.app K := by
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
  exact restriction_proper_comp
    DerivedCategory.Plus.ι DerivedCategory.Plus.ι DerivedCategory.Plus.ι
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g)
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlus
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (f ≫ g))
    (lowerStar (ModuleCat.{u + 1} A) (f ≫ g)).rightDerivedFunctorPlus
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (lowerStar (ModuleCat.{u + 1} A) (f ≫ g)).rightDerivedFunctor
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g))
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility
    (lowerStar (ModuleCat.{u + 1} A) (f ≫ g)).rightDerivedFunctorPlusCompatibility
    (properLowerShriekPlusIso A f) (properLowerShriekPlusIso A g)
    (properLowerShriekPlusIso A (f ≫ g))
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) (f ≫ g))
    (rightDerivedLowerShriekPlusCompIso A f g) (rightDerivedLowerShriekCompIso A f g).symm
    (ProEtale.etaleComparisonDirectImageCompIso A f g)
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl)
    (fun L ↦ proper_plus_hom A f L) (fun L ↦ proper_plus_hom A g L)
    (fun L ↦ proper_plus_hom A (f ≫ g) L)
    (fun L ↦ composition_plus A f g L)
    (fun L ↦ ordinary_plus_compat A f g L) (proper_native_nat A f g) K
/-- The proper compositor equation before evaluation at an object.
Source: the proper forget-supports composition equation above
(blueprint: lem-pur-proper-etale-plus-composition).
Proof: natural-transformation extensionality reduces to the proved component equation. -/
theorem properLowerShriekPlusIso_comp_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] :
    (rightDerivedLowerShriekPlusCompIso A f g).hom ≫
        (properLowerShriekPlusIso A (f ≫ g)).hom =
      Functor.whiskerRight (properLowerShriekPlusIso A f).hom
          (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g) ≫
        Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus
          (properLowerShriekPlusIso A g).hom ≫
        (ProEtale.etaleComparisonDirectImageCompIso A f g).hom := by
  apply NatTrans.ext
  funext K
  exact properLowerShriekPlusIso_comp A f g K

end AlgebraicGeometry.Etale
