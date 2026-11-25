/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.AdjunctionSquareExchange
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

public import Mathlib.CategoryTheory.Sites.LocalSite

/-!
# Canonical closed-test derived exchange maps

Source: Stacks Project, Tags 09BL and 0D6F
(blueprint: def-sfb-closed-test-derived-exchange-maps).

These are the unchanged canonical map constructions previously housed with the
closed-test exchange theorems. Keeping the constructions separate allows those
theorems to import their section-localization proof dependencies without a cycle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel

/-- Cache the existing monoidal structure, without changing its data.
Source: internal-module convention
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance (priority := 2500) condensedMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  inferInstance

/-- Cache the existing pro-etale sheaf monoidal structure, without changing its data.
Source: internal-module convention
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance (priority := 2500) proetaleMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  inferInstance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Cache the recorded abelian structure on the same internal module category.
Source: internal-module and K-injective convention
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance (priority := 2500) moduleAbelian (X : Scheme.{u}) :
    Abelian (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  inferInstance

/-- Cache additivity of the recorded terminal-object sections functor.
The body uses the existing additive forgetful and evaluation instances.
Source: global sections convention
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance (priority := 2500) moduleSectionsAdditive (X : Scheme.{u}) :
    (condensedModuleSections Λ X).Additive :=
  inferInstance

/-- Exact pullback, from the recorded module inverse image.
Source: Tags 09BL and 0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

/-- The canonical derived adjunction with exact inverse image.
Source: Tag 09T5 (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull Λ f ⊣ CondensedRing.moduleObjectDerivedPushforward Λ f :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction

/-- Composition of exact pullbacks, using the recorded ordinary composition.
Source: Tag 09T5 (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull Λ (f ≫ g) ≅ pull Λ g ⋙ pull Λ f :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The canonical pullback comparison of a commutative square.
Source: Tag 09BL, specified mate (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def square {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    pull Λ s ⋙ pull Λ fZ ≅ pull Λ f ⋙ pull Λ h :=
  (pullComp Λ fZ s).symm ≪≫
    eqToIso (congrArg (fun b : T ⟶ U ↦ pull Λ b) w.w.symm) ≪≫ pullComp Λ h f

/-- The specified exchange, constructed as the adjunction mate.
Source: Tag 09BL, unit--counit calculation
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def exchange {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ s ⟶
      pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ :=
  Adjunction.squareExchange (adj Λ f) (adj Λ fZ) (pull Λ s) (pull Λ h) (square Λ w)

/-- Canonical global-section composition before deriving.
Source: Tag 0D6E, sectionwise identity
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def pushSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStar Λ f ⋙ condensedModuleSections Λ Y ≅
      condensedModuleSections Λ X :=
  Functor.isoWhiskerLeft (CondensedRing.lowerStar Λ f)
      (Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ Y))
        (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}
          (Scheme.ProEt.isTerminalMkId Y))).symm ≪≫
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ X))
      (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} f) ≪≫
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ X))
      (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) Ab.{u + 1}
        (Scheme.ProEt.isTerminalMkId X))

/-- K-injective preservation is supplied by the existing exact inverse-image adjunction.
Source: Tag 08BJ (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance lowerStarPreservesKInjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).PreservesKInjectiveComplexes :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes

/-- Derived composition for global sections, normalized by the ordinary section identity.
Source: Tag 0D6E (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def pushDerivedSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
        (condensedModuleSections Λ Y).rightDerivedFunctor ≅
      (condensedModuleSections Λ X).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' _ _ (pushSectionsIso Λ f)

/-- Canonical derived restriction: the derived unit, followed by section composition.
Source: Tags 09T5 and 0D6E
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (condensedModuleSections Λ Y).rightDerivedFunctor ⟶
      pull Λ f ⋙ (condensedModuleSections Λ X).rightDerivedFunctor :=
  Functor.whiskerRight (adj Λ f).unit
      (condensedModuleSections Λ Y).rightDerivedFunctor ≫
    Functor.whiskerLeft (pull Λ f) (pushDerivedSectionsIso Λ f).hom

/-- Derived sections on the source of b, after the existing exact pullback.
For a pro-etale b this is the canonical localized-site derived sections.
Source: Tag 0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def sectionsOver {X W : Scheme.{u}} (b : W ⟶ X) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤ DerivedCategory Ab.{u + 1} :=
  pull Λ b ⋙ (condensedModuleSections Λ W).rightDerivedFunctor

/-- Restriction between two schemes over X, with the canonical pullback composition.
Source: Tags 0D6E--0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictionOver {X W W' : Scheme.{u}} (b : W ⟶ X) (a : W' ⟶ W) :
    sectionsOver Λ b ⟶ sectionsOver Λ (a ≫ b) :=
  Functor.whiskerLeft (pull Λ b) (restriction Λ a) ≫
    Functor.whiskerRight (pullComp Λ a b).inv
      (condensedModuleSections Λ W').rightDerivedFunctor

/-- The canonical Leray/base-change section comparison of a commutative square.
It is defined without an invertibility assumption.
Source: Tags 09BL and 0D6E (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def sectionComparison {X U T W : Scheme.{u}} {f : X ⟶ U} {b : W ⟶ U}
    {h : T ⟶ X} {fW : T ⟶ W} (w : CommSq h fW f b) :
    CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ sectionsOver Λ b ⟶
      sectionsOver Λ h :=
  Functor.whiskerRight (exchange Λ w)
      (condensedModuleSections Λ W).rightDerivedFunctor ≫
    Functor.whiskerLeft (pull Λ h) (pushDerivedSectionsIso Λ fW).hom

/-- Restriction to V from its closed-site lift, along the actual closed inclusion.
The equality uses the geometric pullback statement, not an arbitrary comparison map.
Source: Tag 09BL (2) (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def closedComparison (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    sectionsOver Λ ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom ⟶
      pull Λ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⋙
        sectionsOver Λ V.hom :=
  restrictionOver Λ _ (Scheme.AffineProEt.closedSiteLiftInclusion A I V) ≫
    (eqToIso (congrArg (fun b ↦ sectionsOver Λ b)
      ((Scheme.AffineProEt.affine_closed_site_functor_properties A I).2.2.2.2.2.2.2
        V).2.1.w)).hom ≫
    Functor.whiskerRight (pullComp Λ V.hom
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).hom
      (condensedModuleSections Λ V.left).rightDerivedFunctor

/-- The closed subscheme morphism Spec(A/I) → Spec A.
Source: Tag 09BL (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
abbrev closedMap (A : Type u) [CommRing A] (I : Ideal A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The map from the closed test fibre to its lifted test fibre, by the pullback property.
Source: Tag 09BK (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def testMap (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : CommSq h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    pullback fZ V.hom ⟶ pullback f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom :=
  pullback.lift (pullback.fst fZ V.hom ≫ h)
    (pullback.snd fZ V.hom ≫ Scheme.AffineProEt.closedSiteLiftInclusion A I V)
    (by
      rw [Category.assoc, w.w, ← Category.assoc, pullback.condition, Category.assoc]
      rw [Category.assoc,
        ((Scheme.AffineProEt.affine_closed_site_functor_properties A I).2.2.2.2.2.2.2
          V).2.1.w])

/-- Restriction on the two actual test fibres, including its canonical target identification.
Source: Tags 09BL and 0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def testRestriction (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : CommSq h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    sectionsOver Λ (pullback.fst f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom) ⟶
      pull Λ h ⋙ sectionsOver Λ (pullback.fst fZ V.hom) :=
  restrictionOver Λ _ (testMap A I w V) ≫
    (eqToIso (congrArg (fun b ↦ sectionsOver Λ b)
      (pullback.lift_fst _ _ _))).hom ≫
    Functor.whiskerRight (pullComp Λ (pullback.fst fZ V.hom) h).hom
      (condensedModuleSections Λ (pullback fZ V.hom)).rightDerivedFunctor

end AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel
