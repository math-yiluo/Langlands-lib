/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSiteWordRefinement

/-! # Finite-site comparison of a compatible proper/open tower

Source: Stacks Project, Tags 0F7J and 0F7B, the four composition equalities
(blueprint: lem-sp-finite-site-tower-paste).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
namespace FiniteSiteTower

private local instance tower_has_base_change
    (R : Type (u + 1)) [CommRing R] : (Etale.unboundedFormalism R).HasBaseChange :=
  Etale.unbounded_has_base_change R

private local instance tower_has_proper_exchange
    (R : Type (u + 1)) [CommRing R] [Finite R] :
    (Etale.unboundedFormalism R).HasProperExchange :=
  Etale.unbounded_has_proper_exchange R

variable (R : Type (u + 1)) [CommRing R]

/-- Bounded-below etale coordinates. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
abbrev DE (X : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- Bounded-below pro-etale coordinates. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
abbrev DP (X : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))

/-- Exact site comparison, restricted to D+. Source: Stacks 099R
(blueprint: lem-sp-finite-site-tower-paste). -/
abbrev N (X : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus

/-- Etale direct image on D+. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
abbrev PE {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Etale.lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctorPlus

/-- Pro-etale direct image on D+. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
abbrev PP {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctorPlus

/-- Etale open extension on D+. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
abbrev JE {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus

/-- Pro-etale open extension on D+. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
abbrev JP {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus

/-- The actual two-edge comparison, not an arbitrary isomorphism. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def B {X W Y : Scheme.{u}} (j : X ⟶ W) [IsOpenImmersion j] (r : W ⟶ Y)
    (E : DE R X) :
    (N R Y).obj ((PE R r).obj ((JE R j).obj E)) ⟶
      (PP R r).obj ((JP R j).obj ((N R X).obj E)) :=
  (fixedComparisonDirectImageMatePlus R r).app ((JE R j).obj E) ≫
    (PP R r).map ((properOpenSiteExtensionIso R j).hom.app E)

/-- The canonical etale proper compositor, normalized by inverse adjunction conjugacy.
Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def kE {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    PE R a ⋙ PE R b ≅ PE R (a ≫ b) :=
  (conjugateIsoEquiv
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) (a ≫ b))
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) b).comp
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) a))
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} R) a b).symm).symm

/-- The canonical pro-etale proper compositor, normalized by inverse adjunction conjugacy.
Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def kP {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    PP R a ⋙ PP R b ≅ PP R (a ≫ b) :=
  (conjugateIsoEquiv
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) (a ≫ b))
    ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) b).comp
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) a))
    (Functor.mapDerivedCategoryPlusNatIso
      (upperStarComp (ModuleCat.{u + 1} R) a b) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _).symm).symm

/-- Canonical etale open compositor. Source: Stacks 03EH
(blueprint: lem-sp-finite-site-tower-paste). -/
def mE {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b] : JE R a ⋙ JE R b ≅ JE R (a ≫ b) :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} R) a b).symm

/-- Canonical pro-etale open compositor. Source: Stacks 03EH
(blueprint: lem-sp-finite-site-tower-paste). -/
def mP {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b] : JP R a ⋙ JP R b ≅ JP R (a ≫ b) :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (proEtaleOpenExtensionComp R a b).symm

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem comp_square {C : Type*} [Category C]
    {A B C' D E F : C} {l : A ⟶ B} {m : C' ⟶ D} {r : E ⟶ F}
    {f : A ⟶ C'} {f' : B ⟶ D} {g : C' ⟶ E} {g' : D ⟶ F}
    (hf : l ≫ f' = f ≫ m) (hg : m ≫ g' = g ≫ r) :
    l ≫ (f' ≫ g') = (f ≫ g) ≫ r := by
  rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem map_square {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {A B C' D' : C}
    {l : A ⟶ B} {r : C' ⟶ D'} {f : A ⟶ C'} {g : B ⟶ D'}
    (h : l ≫ g = f ≫ r) : P.map l ≫ P.map g = P.map f ≫ P.map r := by
  rw [← P.map_comp, h, P.map_comp]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem B_naturality {X W Y : Scheme.{u}} (j : X ⟶ W)
    [IsOpenImmersion j] (r : W ⟶ Y) {E F : DE R X} (h : E ⟶ F) :
    (N R Y).map ((PE R r).map ((JE R j).map h)) ≫ B R j r F =
      B R j r E ≫ (PP R r).map ((JP R j).map ((N R X).map h)) := by
  simpa only [finiteSiteWordComparison, B, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.comp_map,
    Etale.rightDerivedLowerStarPlus, N, PE, PP, JE, JP] using
    (finiteSiteWordComparison R j r).naturality h

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem conjugate_iso_reverse
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₂ ≅ L₁) :
    (conjugateIsoEquiv a b e).symm = conjugateIsoEquiv b a e.symm := by
  rfl

variable [Finite R]
variable {X U XB Y YB Z : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian U] [IsNoetherian XB]
  [IsNoetherian Y] [IsNoetherian YB] [IsNoetherian Z]
  (a : X ⟶ U) (b : U ⟶ XB) (p : XB ⟶ YB) (q : YB ⟶ Z)
  (i : Y ⟶ YB) (s : U ⟶ Y)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion i]
  [QuasiCompact a] [QuasiCompact b] [QuasiCompact i]
  [IsProper p] [IsProper q] [IsProper s]
  (sq : IsPullback b s p i)

/-- The etale interchange before the compositors. Source: Stacks 0F7B
(blueprint: lem-sp-finite-site-tower-paste). -/
def GE (E : DE R X) :=
  (Etale.properOpenCoefficientInterchangePlus R sq ((JE R a).obj E)).hom

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem GE_naturality {E F : DE R X} (h : E ⟶ F) :
    (JE R i).map ((PE R s).map ((JE R a).map h)) ≫ GE R a b p i s sq F =
      GE R a b p i s sq E ≫ (PE R p).map ((JE R b).map ((JE R a).map h)) := by
  simpa only [GE, Etale.properOpenCoefficientInterchangePlusIso_app, Functor.comp_map]
    using (Etale.properOpenCoefficientInterchangePlusIso R sq).hom.naturality
      ((JE R a).map h)

/-- The open-adjunct pro-etale interchange on J_a N E. Transport along the canonical
open comparison changes the origin witness from N J_a E to J_a N E. This uses the
specified adjunct, never the tower comparison equation. Source: Stacks 0F7B
(blueprint: lem-sp-finite-site-tower-paste). -/
def GP (E : DE R X) :=
  (JP R i).map ((PP R s).map ((properOpenSiteExtensionIso R a).inv.app E)) ≫
    properOpenSiteInterchange R sq ((JE R a).obj E) ≫
    (PP R p).map ((JP R b).map ((properOpenSiteExtensionIso R a).hom.app E))

/-- The actual etale tower arrow, including both canonical compositors.
Source: Stacks 0F7J (blueprint: lem-sp-finite-site-tower-paste). -/
def AE (E : DE R X) :=
  (PE R q).map (GE R a b p i s sq E) ≫
    (kE R p q).hom.app ((JE R b).obj ((JE R a).obj E)) ≫
    (PE R (p ≫ q)).map ((mE R a b).hom.app E)

/-- The actual pro-etale open-adjunct tower paste. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def AP (E : DE R X) :=
  (PP R q).map (GP R a b p i s sq E) ≫
    (kP R p q).hom.app ((JP R b).obj ((JP R a).obj ((N R X).obj E))) ≫
    (PP R (p ≫ q)).map ((mP R a b).hom.app ((N R X).obj E))

/-- Input word comparison, with its four specified factors. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def Win (E : DE R X) :=
  (fixedComparisonDirectImageMatePlus R q).app
      ((JE R i).obj ((PE R s).obj ((JE R a).obj E))) ≫
    (PP R q).map ((properOpenSiteExtensionIso R i).hom.app
      ((PE R s).obj ((JE R a).obj E))) ≫
    (PP R q).map ((JP R i).map
      ((fixedComparisonDirectImageMatePlus R s).app ((JE R a).obj E))) ≫
    (PP R q).map ((JP R i).map ((PP R s).map
      ((properOpenSiteExtensionIso R a).hom.app E)))

/-- Output word comparison, with its four specified factors. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def Wout (E : DE R X) :=
  (fixedComparisonDirectImageMatePlus R q).app
      ((PE R p).obj ((JE R b).obj ((JE R a).obj E))) ≫
    (PP R q).map ((fixedComparisonDirectImageMatePlus R p).app
      ((JE R b).obj ((JE R a).obj E))) ≫
    (PP R q).map ((PP R p).map
      ((properOpenSiteExtensionIso R b).hom.app ((JE R a).obj E))) ≫
    (PP R q).map ((PP R p).map ((JP R b).map
      ((properOpenSiteExtensionIso R a).hom.app E)))

/-- The comparison of the two compact-support factors. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def D (E : DE R X) :=
  B R i q ((PE R s).obj ((JE R a).obj E)) ≫
    (PP R q).map ((JP R i).map (B R a s E))

/-- The unbounded etale proper/open tower, with the canonical conjugate and open
compositors. This is the normalized tower prescription of
lem-amb-unbounded-compact-support-comparisons, not an arbitrary isomorphism.
Source: Stacks 0F7J (blueprint: lem-sp-finite-site-tower-paste). -/
def AEUnbounded (E : Etale.DerivedCategoryModule R X) :=
  (Etale.lowerStar (ModuleCat.{u + 1} R) q).rightDerivedFunctor.map
      ((Etale.properOpenCoefficientInterchange R sq).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a).mapDerivedCategory.obj E)) ≫
    (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} R) p q).hom.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) b).mapDerivedCategory.obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a).mapDerivedCategory.obj E)) ≫
    (Etale.lowerStar (ModuleCat.{u + 1} R) (p ≫ q)).rightDerivedFunctor.map
      ((Functor.mapDerivedCategoryCompIso _ _).hom.app E ≫
        (Functor.mapDerivedCategoryNatIso
          (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} R) a b).symm).hom.app E)

/-- Compatibility of the source word with the fully faithful inclusion D+ into D.
Source: Stacks 0F7J (blueprint: lem-sp-finite-site-tower-paste). -/
def sourceCompatibility (E : DE R X) :=
  ((Etale.lowerStar (ModuleCat.{u + 1} R) q).rightDerivedFunctorPlusCompatibility.app
      ((JE R i).obj ((PE R s).obj ((JE R a).obj E)))) ≪≫
    (Etale.lowerStar (ModuleCat.{u + 1} R) q).rightDerivedFunctor.mapIso
      (((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} R) i).mapDerivedCategoryPlusCompatibility.app
          ((PE R s).obj ((JE R a).obj E))) ≪≫
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) i).mapDerivedCategory.mapIso
          (((Etale.lowerStar (ModuleCat.{u + 1} R) s).rightDerivedFunctorPlusCompatibility.app
              ((JE R a).obj E)) ≪≫
            (Etale.lowerStar (ModuleCat.{u + 1} R) s).rightDerivedFunctor.mapIso
              ((Etale.openImmersionLowerShriek
                (ModuleCat.{u + 1} R) a).mapDerivedCategoryPlusCompatibility.app E)))

/-- Compatibility of the target compact-support word with D+ inclusion.
Source: Stacks 0F7J (blueprint: lem-sp-finite-site-tower-paste). -/
def targetCompatibility (E : DE R X) :=
  ((Etale.lowerStar (ModuleCat.{u + 1} R) (p ≫ q)).rightDerivedFunctorPlusCompatibility.app
      ((JE R (a ≫ b)).obj E)) ≪≫
    (Etale.lowerStar (ModuleCat.{u + 1} R) (p ≫ q)).rightDerivedFunctor.mapIso
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} R) (a ≫ b)).mapDerivedCategoryPlusCompatibility.app E)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem kE_restriction
    (E : DE R XB) :
    DerivedCategory.Plus.ι.map ((kE R p q).hom.app E) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} R)
        (p ≫ q)).rightDerivedFunctorPlusCompatibility.hom.app E =
    (Etale.lowerStar (ModuleCat.{u + 1} R) q).rightDerivedFunctorPlusCompatibility.hom.app
        ((PE R p).obj E) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} R) q).rightDerivedFunctor.map
        ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctorPlusCompatibility.hom.app E) ≫
      (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} R) p q).hom.app E.obj := by
  have he : etaleComparisonDirectImageCompIso R p q = kE R p q := by
    rw [(finiteSiteWordRefinement R).2.2.2.2.1 p q |>.1, kE, conjugate_iso_reverse]
    rfl
  rw [← he]
  simpa only [PE, ObjectProperty.ι_obj, Functor.comp_obj,
    etaleComparisonDirectImageCompIso, Etale.right_derived_star_comp_eq] using
    Etale.right_derived_comp_prime_plus
      (Etale.lowerStar (ModuleCat.{u + 1} R) p)
      (Etale.lowerStar (ModuleCat.{u + 1} R) q)
      (Etale.lowerStarComp (ModuleCat.{u + 1} R) p q) E

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem mE_restriction (E : DE R X) :
    DerivedCategory.Plus.ι.map ((mE R a b).hom.app E) =
      (Functor.mapDerivedCategoryCompIso
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a)
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) b)).hom.app E.obj ≫
      (Functor.mapDerivedCategoryNatIso
        (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} R) a b).symm).hom.app E.obj := by
  have hc : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusCompIso
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a)
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) b)).app E) =
      (Functor.mapDerivedCategoryCompIso
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a)
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) b)).symm.app E.obj := by
    apply Iso.ext
    exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ E
  simp only [mE, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact congrArg (fun t ↦ t ≫ _) (congrArg Iso.inv hc)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem GE_restriction (E : DE R X) :
    DerivedCategory.Plus.ι.map (GE R a b p i s sq E) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctorPlusCompatibility.hom.app
        ((JE R b).obj ((JE R a).obj E)) =
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) i).mapDerivedCategory.map
      ((Etale.lowerStar (ModuleCat.{u + 1} R) s).rightDerivedFunctorPlusCompatibility.hom.app
        ((JE R a).obj E)) ≫
      (Etale.properOpenCoefficientInterchange R sq).hom.app ((JE R a).obj E).obj := by
  simp only [GE, Etale.properOpenCoefficientInterchangePlus, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Etale.properOpenCoefficientTargetPlus,
    Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc,
    Iso.inv_hom_id_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, JE,
    ObjectProperty.ι_obj, Functor.comp_obj, Category.comp_id]
  erw [(Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.map_id,
    Category.comp_id]
  simp only [Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The etale arrow is the restriction of the normalized unbounded tower compositor.
Source: Stacks 0F7J; lem-amb-unbounded-compact-support-comparisons, tower normalization
(blueprint: lem-sp-finite-site-tower-paste).
Proof: use the canonical inclusion compatibilities for each proper and open factor.
The definition of properOpenCoefficientInterchangePlus restricts precisely the
specified unbounded Gamma. The derived proper and exact open compositors restrict
along the same fully faithful inclusion. Paste these three squares. The unbounded
tower normalization identifies AEUnbounded with the compact-support compositor
on the supplied compatible tower, so this states its bounded-below restriction. -/
theorem etale_normalization (E : DE R X) :
    DerivedCategory.Plus.ι.map (AE R a b p q i s sq E) ≫
        (targetCompatibility R a b p q E).hom =
      (sourceCompatibility R a q i s E).hom ≫ AEUnbounded R a b p q i s sq E.obj := by
  have hk := kE_restriction R p q ((JE R b).obj ((JE R a).obj E))
  have hm := mE_restriction R a b E
  have hg := GE_restriction R a b p i s sq E
  have hn := NatTrans.naturality
    (Etale.lowerStar (ModuleCat.{u + 1} R)
      (p ≫ q)).rightDerivedFunctorPlusCompatibility.hom ((mE R a b).hom.app E)
  have hq := NatTrans.naturality
    (Etale.lowerStar (ModuleCat.{u + 1} R) q).rightDerivedFunctorPlusCompatibility.hom
    (GE R a b p i s sq E)
  dsimp only [Functor.comp_map] at hn hq
  simp only [AE, AEUnbounded, targetCompatibility, sourceCompatibility,
    Functor.map_comp, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom,
    NatTrans.id_app] at hg ⊢
  erw [reassoc_of% hn, reassoc_of% hk, reassoc_of% hq]
  rw [← Functor.map_comp_assoc, hg, Functor.map_comp, hm]
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp, Category.assoc, JE, PE, Functor.comp_obj]
  rfl

/-- The supplied compactification `(a, s)` of `f = a ≫ s`. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def compactificationF : Compactification (a ≫ s) where
  Z := U
  g := s
  i := a
  comm := rfl
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The supplied compactification `(i, q)` of `g = i ≫ q`. Source: Stacks 0F7J
(blueprint: lem-sp-finite-site-tower-paste). -/
def compactificationG : Compactification (i ≫ q) where
  Z := YB
  g := q
  i := i
  comm := rfl
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The supplied compactification `(a ≫ b, p ≫ q)` of `g f`, using `b ≫ p = s ≫ i`.
Source: Stacks 0F7J (blueprint: lem-sp-finite-site-tower-paste). -/
def compactificationGF : Compactification ((a ≫ s) ≫ (i ≫ q)) where
  Z := XB
  g := p ≫ q
  i := a ≫ b
  comm := by simp only [Category.assoc, sq.w_assoc]
  isProper := inferInstance
  isOpenImmersion := inferInstance

private def towerTriangle : Compactification.Triangle (a ≫ s) (i ≫ q) where
  cf := compactificationF a s
  cg := compactificationG q i
  cfg := compactificationGF a b p q i s sq
  q := b
  p := p
  i_q := rfl
  p_g := rfl
  isPullback := sq.flip

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem interchange_eq_exchange (M : Etale.DerivedCategoryModule R U) :
    (Etale.properOpenCoefficientInterchange R sq).hom.app M =
      (Etale.openImmersionLowerShriekLowerStarExchange
        (ModuleCat.{u + 1} R) sq.flip).app M := by
  obtain ⟨lam, hl, hg⟩ :=
    (Etale.properOpenCoefficientInterchange_normalized_exists R sq).choose_spec
  rw [show (Etale.properOpenCoefficientInterchange R sq).hom.app M = _ from hg M]
  symm
  apply Etale.adjunct_eq_inverse
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) i) _ (lam.app M)
  have ht := Etale.unboundedEtaleCompactSupport_tower_adjunct R sq M
  simpa only [Etale.unboundedEtaleProperOpenRestriction, hl, Iso.app_hom,
    Etale.rightDerivedLowerStar, asIso_inv, NatIso.isIso_inv_app, Functor.comp_obj] using ht

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem AEUnbounded_eq_triangle (M : Etale.DerivedCategoryModule R X) :
    AEUnbounded R a b p q i s sq M =
      ((Etale.unboundedFormalism R).compIso
        (towerTriangle a b p q i s sq)).hom.app M := by
  rw [Etale.unbounded_comp_hom_app]
  dsimp only [towerTriangle, compactificationF, compactificationG, compactificationGF]
  rw [Etale.right_derived_star_comp_eq]
  simp only [Etale.mapDerivedCategoryOpenImmersionLowerShriekComp,
    Etale.mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, Iso.trans_inv,
    NatTrans.comp_app, Functor.map_comp]
  unfold AEUnbounded
  rw [interchange_eq_exchange R b p i s sq]
  have hn := (Etale.rightDerivedLowerStarComp
    (ModuleCat.{u + 1} R) p q).hom.naturality
      ((Functor.mapDerivedCategoryCompIso
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a)
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) b)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        (Etale.openImmersionLowerShriekComp
          (ModuleCat.{u + 1} R) a b).symm).hom.app M)
  dsimp only [Functor.comp_map] at hn
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryNatIso_symm, Iso.symm_hom, Iso.symm_inv,
    Etale.rightDerivedLowerStar] using
    congrArg (fun t ↦ (Etale.lowerStar (ModuleCat.{u + 1} R) q).rightDerivedFunctor.map
      ((Etale.openImmersionLowerShriekLowerStarExchange
        (ModuleCat.{u + 1} R) sq.flip).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} R) a).mapDerivedCategory.obj M)) ≫ t) hn.symm

set_option maxRecDepth 4096 in
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem B_isIso {X W Y : Scheme.{u}} (j : X ⟶ W)
    [IsOpenImmersion j] (r : W ⟶ Y) [QuasiCompact r] [QuasiSeparated r]
    (E : DE R X) : IsIso (B R j r E) := by
  have := isIso_fixedComparisonDirectImageMatePlus R r
  unfold B
  infer_instance

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem AE_isIso (E : DE R X) : IsIso (AE R a b p q i s sq E) := by
  have : IsIso (GE R a b p i s sq E) := by unfold GE; infer_instance
  unfold AE
  infer_instance

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem compositor_equation (E : DE R X) :
    (N R Z).map
        ((kE R p q).hom.app ((JE R b).obj ((JE R a).obj E)) ≫
          (PE R (p ≫ q)).map ((mE R a b).hom.app E)) ≫
        B R (a ≫ b) (p ≫ q) E =
      Wout R a b p q E ≫
        (kP R p q).hom.app ((JP R b).obj ((JP R a).obj ((N R X).obj E))) ≫
          (PP R (p ≫ q)).map ((mP R a b).hom.app ((N R X).obj E)) := by
  have hp := (finiteSiteWordRefinement R).2.2.2.2.2.1 p q
    ((JE R b).obj ((JE R a).obj E))
  have ho := (finiteSiteWordRefinement R).2.2.2.2.2.2.2.1 a b E
  have hn := (finiteSiteWordRefinement R).2.2.2.2.1 p q
  have he : etaleComparisonDirectImageCompIso R p q = kE R p q := by
    rw [hn.1, kE, conjugate_iso_reverse]
    rfl
  have hp' : proEtaleComparisonDirectImageCompIso R p q = kP R p q := by
    rw [hn.2, kP, conjugate_iso_reverse]
    rfl
  rw [he, hp'] at hp
  change (N R Z).map ((kE R p q).hom.app ((JE R b).obj ((JE R a).obj E))) ≫
      (fixedComparisonDirectImageMatePlus R (p ≫ q)).app
        ((JE R b).obj ((JE R a).obj E)) =
    (fixedComparisonDirectImageMatePlus R q).app
        ((PE R p).obj ((JE R b).obj ((JE R a).obj E))) ≫
      (PP R q).map ((fixedComparisonDirectImageMatePlus R p).app
        ((JE R b).obj ((JE R a).obj E))) ≫
      (kP R p q).hom.app ((N R XB).obj ((JE R b).obj ((JE R a).obj E))) at hp
  change (N R XB).map ((mE R a b).hom.app E) ≫
      (properOpenSiteExtensionIso R (a ≫ b)).hom.app E =
    (properOpenSiteExtensionIso R b).hom.app ((JE R a).obj E) ≫
      (JP R b).map ((properOpenSiteExtensionIso R a).hom.app E) ≫
      (mP R a b).hom.app ((N R X).obj E) at ho
  have hd := (fixedComparisonDirectImageMatePlus R (p ≫ q)).naturality
    ((mE R a b).hom.app E)
  have hk := (kP R p q).hom.naturality
    ((properOpenSiteExtensionIso R b).hom.app ((JE R a).obj E) ≫
      (JP R b).map ((properOpenSiteExtensionIso R a).hom.app E))
  dsimp only [Functor.comp_map] at hd hk
  unfold B Wout
  dsimp only [N, PE, Etale.rightDerivedLowerStarPlus, PP, JE, JP] at hp ho hd hk ⊢
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hd]
  slice_lhs 3 4 =>
    erw [← (PP R (p ≫ q)).map_comp, ho, Functor.map_comp, Functor.map_comp]
  erw [reassoc_of% hp]
  simpa only [N, PE, PP, JE, JP, Etale.rightDerivedLowerStarPlus, Functor.comp_obj,
    properOpenSiteExtensionIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦
      (fixedComparisonDirectImageMatePlus R q).app
          ((PE R p).obj ((JE R b).obj ((JE R a).obj E))) ≫
        (PP R q).map ((fixedComparisonDirectImageMatePlus R p).app
          ((JE R b).obj ((JE R a).obj E))) ≫ t ≫
        (PP R (p ≫ q)).map ((mP R a b).hom.app ((N R X).obj E))) hk.symm

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem word_equation (E : DE R X) :
    (N R Z).map ((PE R q).map (GE R a b p i s sq E)) ≫ Wout R a b p q E =
      Win R a q i s E ≫ (PP R q).map (GP R a b p i s sq E) := by
  have hs := DerivedCategory.Plus.ι.map_injective
    (properOpen_site_mate R sq ((JE R a).obj E))
  have hd := (fixedComparisonDirectImageMatePlus R q).naturality
    (GE R a b p i s sq E)
  have ht := congrArg (fun t ↦
    (fixedComparisonDirectImageMatePlus R q).app
      ((JE R i).obj ((PE R s).obj ((JE R a).obj E))) ≫
    (PP R q).map (t ≫
      (PP R p).map ((JP R b).map ((properOpenSiteExtensionIso R a).hom.app E)))) hs
  dsimp only [properOpenSiteComposite, Functor.comp_map] at ht hd
  unfold Wout Win GP
  dsimp only [PE, Etale.rightDerivedLowerStarPlus, N, PP, JE, JP] at ht hd ⊢
  simp only [Functor.map_comp, Category.assoc] at ht ⊢
  rw [reassoc_of% hd]
  refine ht.trans ?_
  slice_rhs 4 5 =>
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    erw [(PP R s).map_id, (JP R i).map_id, (PP R q).map_id]
  simp only [Category.id_comp]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite-site word equation, its compositor paste and the resulting inverse formula.
Source: Stacks 0F7J, four equalities, and 0F7B
(blueprint: lem-sp-finite-site-tower-paste).

Proof: (1) lem-sp-finite-site-word-refinement supplies lower bounds and invertibility
of the three B maps. (2) Apply lem-sp-proper-open-coefficient-mate to M = J_a E.
(3) Whisker its site square by P_q and use naturality of d_q and of the open adjunct
at e_a(E); this is the word equation. (4) Expand B_g and B_f to identify D with Win.
(5) Apply the proper and open compositor equations of word-refinement, and naturality
of d_(qp), to identify C^p Wout with B_gf N(C^e). (6) Postcompose the word equation
by C^p to obtain the named-map equation. (7) The normalization of
lem-amb-unbounded-compact-support-comparisons identifies AE with the restriction
of the unbounded etale compositor. AE, B_gf and D are invertible; cancel D to get
the displayed transport formula and invertibility of the actual adjunct paste. -/
theorem paste (E : DE R X) :
    (N R Z).map ((PE R q).map (GE R a b p i s sq E)) ≫ Wout R a b p q E =
      Win R a q i s E ≫ (PP R q).map (GP R a b p i s sq E) ∧
    (N R Z).map (AE R a b p q i s sq E) ≫ B R (a ≫ b) (p ≫ q) E =
      D R a q i s E ≫ AP R a b p q i s sq E ∧
    IsIso (AP R a b p q i s sq E) ∧ IsIso (D R a q i s E) ∧
    IsIso (B R a s E) ∧
    IsIso (B R i q ((PE R s).obj ((JE R a).obj E))) ∧
    IsIso (B R (a ≫ b) (p ≫ q) E) ∧
    ∀ h : IsIso (D R a q i s E), AP R a b p q i s sq E =
      @inv _ _ _ _ (D R a q i s E) h ≫ (N R Z).map (AE R a b p q i s sq E) ≫
        B R (a ≫ b) (p ≫ q) E := by
  have hw := word_equation R a b p q i s sq E
  have hc := compositor_equation R a b p q E
  have hD : D R a q i s E = Win R a q i s E := by
    simp only [D, B, Win, Functor.map_comp, Category.assoc]
  have ht : (N R Z).map (AE R a b p q i s sq E) ≫ B R (a ≫ b) (p ≫ q) E =
      D R a q i s E ≫ AP R a b p q i s sq E := by
    unfold AE AP
    simp only [Functor.map_comp, Category.assoc]
    slice_lhs 2 3 => rw [← (N R Z).map_comp]
    rw [hc]
    simp only [← Category.assoc]
    rw [hw, ← hD]
  have hf := B_isIso R a s E
  have hg := B_isIso R i q ((PE R s).obj ((JE R a).obj E))
  have hgf := B_isIso R (a ≫ b) (p ≫ q) E
  have hd : IsIso (D R a q i s E) := by unfold D; infer_instance
  have hinv (h : IsIso (D R a q i s E)) : AP R a b p q i s sq E =
      @inv _ _ _ _ (D R a q i s E) h ≫ (N R Z).map (AE R a b p q i s sq E) ≫
        B R (a ≫ b) (p ≫ q) E := by
    apply (cancel_epi (D R a q i s E)).mp
    simpa only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp] using ht.symm
  have ha := AE_isIso R a b p q i s sq E
  have hap : IsIso (AP R a b p q i s sq E) := by rw [hinv hd]; infer_instance
  exact ⟨hw, ht, hap, hd, hf, hg, hgf, hinv⟩

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of both word comparisons and of the etale tower arrow.
Source: Stacks 0F7J (blueprint: lem-sp-finite-site-tower-paste).
Proof: each d is a natural transformation and each e is a natural isomorphism.
Whiskering them with P and J and composing gives naturality of Win and Wout.
The specified etale interchange is natural, by its unbounded natural isomorphism
and the fully faithful D+ inclusion. Compose its naturality with that of the
proper and open compositors to obtain the last equality. These are the naturality
assertions used in proof Steps 3--7 of the node. -/
theorem word_naturality {E F : DE R X} (h : E ⟶ F) :
    ((N R Z).map ((PE R q).map ((JE R i).map ((PE R s).map ((JE R a).map h)))) ≫
        Win R a q i s F =
      Win R a q i s E ≫
        (PP R q).map ((JP R i).map ((PP R s).map ((JP R a).map ((N R X).map h))))) ∧
    ((N R Z).map ((PE R q).map ((PE R p).map ((JE R b).map ((JE R a).map h)))) ≫
        Wout R a b p q F =
      Wout R a b p q E ≫
        (PP R q).map ((PP R p).map ((JP R b).map ((JP R a).map ((N R X).map h))))) ∧
    (PE R q).map ((JE R i).map ((PE R s).map ((JE R a).map h))) ≫
        AE R a b p q i s sq F =
      AE R a b p q i s sq E ≫ (PE R (p ≫ q)).map ((JE R (a ≫ b)).map h) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Win
    exact comp_square
      ((fixedComparisonDirectImageMatePlus R q).naturality
        ((JE R i).map ((PE R s).map ((JE R a).map h))))
      (comp_square
        (map_square (PP R q) ((properOpenSiteExtensionIso R i).hom.naturality
          ((PE R s).map ((JE R a).map h))))
        (comp_square
          (map_square (PP R q) (map_square (JP R i)
            ((fixedComparisonDirectImageMatePlus R s).naturality ((JE R a).map h))))
          (map_square (PP R q) (map_square (JP R i) (map_square (PP R s)
            ((properOpenSiteExtensionIso R a).hom.naturality h))))))
  · unfold Wout
    exact comp_square
      ((fixedComparisonDirectImageMatePlus R q).naturality
        ((PE R p).map ((JE R b).map ((JE R a).map h))))
      (comp_square
        (map_square (PP R q) ((fixedComparisonDirectImageMatePlus R p).naturality
          ((JE R b).map ((JE R a).map h))))
        (comp_square
          (map_square (PP R q) (map_square (PP R p)
            ((properOpenSiteExtensionIso R b).hom.naturality ((JE R a).map h))))
          (map_square (PP R q) (map_square (PP R p) (map_square (JP R b)
            ((properOpenSiteExtensionIso R a).hom.naturality h))))))
  · unfold AE
    exact comp_square (map_square (PE R q) (GE_naturality R a b p i s sq h))
      (comp_square ((kE R p q).hom.naturality ((JE R b).map ((JE R a).map h)))
        (map_square (PE R (p ≫ q)) ((mE R a b).hom.naturality h)))

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of the three named compact-support comparisons and their input paste.
Source: Stacks 0F7J (blueprint: lem-sp-finite-site-tower-paste).
Proof: expand B as the specified natural mate d followed by P of the natural
open comparison e. Their naturality gives each of the first three equations.
Apply P_q J_i to the first, compose with the second, and use functoriality;
this gives the last equation, also the naturality of Win by proof Step 4.
Thus the transport formula is natural as well, because an inverse of a natural
isomorphism is natural. No transported formula defines the actual AP arrow. -/
theorem comparison_naturality {E F : DE R X} (h : E ⟶ F) :
    ((N R Y).map ((PE R s).map ((JE R a).map h)) ≫ B R a s F =
      B R a s E ≫ (PP R s).map ((JP R a).map ((N R X).map h))) ∧
    ((N R Z).map ((PE R q).map ((JE R i).map ((PE R s).map ((JE R a).map h)))) ≫
        B R i q ((PE R s).obj ((JE R a).obj F)) =
      B R i q ((PE R s).obj ((JE R a).obj E)) ≫
        (PP R q).map ((JP R i).map
          ((N R Y).map ((PE R s).map ((JE R a).map h))))) ∧
    ((N R Z).map ((PE R (p ≫ q)).map ((JE R (a ≫ b)).map h)) ≫
        B R (a ≫ b) (p ≫ q) F =
      B R (a ≫ b) (p ≫ q) E ≫
        (PP R (p ≫ q)).map ((JP R (a ≫ b)).map ((N R X).map h))) ∧
    (N R Z).map ((PE R q).map ((JE R i).map ((PE R s).map ((JE R a).map h)))) ≫
        D R a q i s F =
      D R a q i s E ≫
        (PP R q).map ((JP R i).map ((PP R s).map ((JP R a).map ((N R X).map h)))) := by
  refine ⟨B_naturality R a s h, B_naturality R i q ((PE R s).map ((JE R a).map h)),
    B_naturality R (a ≫ b) (p ≫ q) h, ?_⟩
  unfold D
  exact comp_square (B_naturality R i q ((PE R s).map ((JE R a).map h)))
    (map_square (PP R q) (map_square (JP R i) (B_naturality R a s h)))

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of the actual tower paste, rather than merely of its transported value.
Source: Stacks 0F7J (blueprint: lem-sp-finite-site-tower-paste).
Proof: the inverse open comparison, properOpenSiteInterchange, both direct-image
functors and the two compositors are natural. Compose their naturality equalities.
The naturality of the middle adjunct follows from naturality of the restriction
exchange, open unit, and open-adjunction Hom bijection, as in proof Step 3. -/
theorem paste_naturality {E F : DE R X} (h : E ⟶ F) :
    (PP R q).map ((JP R i).map ((PP R s).map ((JP R a).map ((N R X).map h)))) ≫
        AP R a b p q i s sq F =
      AP R a b p q i s sq E ≫
        (PP R (p ≫ q)).map ((JP R (a ≫ b)).map ((N R X).map h)) := by
  have pe := paste R a b p q i s sq E
  have pf := paste R a b p q i s sq F
  have := pe.2.2.2.1
  apply (cancel_epi (D R a q i s E)).mp
  have hn := comparison_naturality R a b p q i s h
  have ha := (word_naturality R a b p q i s sq h).2.2
  have ht := comp_square (map_square (N R Z) ha) hn.2.2.1
  rw [pe.2.1, pf.2.1] at ht
  rw [← Category.assoc, ← hn.2.2.2, Category.assoc, ht]
  simp only [Category.assoc]

end FiniteSiteTower
end AlgebraicGeometry.ProEtale
