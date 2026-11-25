/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.SiteRelocalizationKInjective
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.SiteRestrictionKInjective
import WeilConjectures.CategoryTheory.SiteModuleExtensionByZeroExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Derived direct images for subterminal slices

Source: Stacks Project, Tags 03CE, 08DG, 08FI and 09T5
(blueprint: lem-sp-subterminal-derived-image-calculus).

The auxiliary records package chosen derived functors with their localization comparisons.
Every functor on module sheaves is the existing Mathlib functor, including its scalar map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u r w a b va vb wa wb

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SubterminalImageCalculus

/-- Pushforward acts additively componentwise. Source: Stacks 03CE, module specialization
(blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance pushforwardAdditive
    {C : Type a} [Category.{va} C] {D : Type b} [Category.{vb} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    (SheafOfModules.pushforward.{w} φ).Additive where
  map_add := rfl

/-- Restriction is the additive pushforward along the forgetful functor.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance overAdditive {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (Z : C) :
    (SheafOfModules.overFunctor.{w} R Z).Additive := pushforwardAdditive (𝟙 _)

/-- Relocalization is additive on sectionwise maps.
Source: Stacks 03DH (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance overMapAdditive {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {X Y : C} (f : X ⟶ Y) :
    (SheafOfModules.overMap.{w} R f).Additive :=
  pushforwardAdditive (Sheaf.pushforwardOverMapIso R f).inv

/-- A chosen derived restriction/direct-image adjunction, normalized on complexes.
Source: Stacks 08FI, 070I, 070K and 09T5
(blueprint: lem-sp-subterminal-derived-image-calculus).
The two preservation fields and two resolution fields are assertions, not assumptions
on the site. The comparison `qG` computes direct image on K-injective complexes.
The last field fixes the derived adjunction to the ordinary chain-map transpose. -/
structure DerivedPair
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (ordinary : F ⊣ G) where
  left : DerivedCategory A ⥤ DerivedCategory B
  right : DerivedCategory B ⥤ DerivedCategory A
  adj : left ⊣ right
  qF : DerivedCategory.Q ⋙ left ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  qG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ right
  qG_iso : ∀ (I : CochainComplex B ℤ), I.IsKInjective → IsIso (qG.app I)
  restrict_injective : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
    CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I)
  direct_injective : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
    CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I)
  resolutions_source : ∀ (M : CochainComplex A ℤ),
    ∃ (I : CochainComplex A ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective
  resolutions_target : ∀ (M : CochainComplex B ℤ),
    ∃ (I : CochainComplex B ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective
  transpose : ∀ (M : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I), I.IsKInjective →
    adj.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
        (qF.hom.app M ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((ordinary.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
        qG.app I

/-- The actual sectionwise right adjoint, evaluating at `Z × C → Z` (the product order
used by Mathlib's `Over.star`). The scalar map is restriction along the other projection.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev direct {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{max u r}) (Z : C) :=
  SheafOfModules.pushforward.{max u r} (SheafOfModules.pushforwardOver (R := R) Z)

/-- The overlap map is the transpose of the restricted counit.
Source: Stacks 08DG (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def overlap {A : Type a} [Category.{va} A]
    {B : Type b} [Category.{vb} B] {D : Type w} [Category.{r} D]
    {f : A ⥤ B} {g : B ⥤ A} {h : A ⥤ D} {k : D ⥤ A} {t : B ⥤ D}
    (adj : f ⊣ g) (adjW : h ⊣ k) (comp : h ≅ f ⋙ t) (X : B) :
    g.obj X ⟶ k.obj (t.obj X) :=
  adjW.homEquiv _ _ (comp.hom.app (g.obj X) ≫ t.map (adj.counit.app X))

/-- The forgetful change from commutative ring sheaves to ring sheaves.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev ring {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) : Sheaf J RingCat.{max u r} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

/-- The recorded module category, with coefficient and site universes both retained.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) := ringedSiteModules.{max u r} (ring R)

/-- The recorded module category on the localized ringed site.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev sliceModules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) (Z : C) :=
  ringedSiteModules.{max u r} ((ring.{u, r} R).over Z)

set_option synthInstance.maxHeartbeats 100000 in
-- Additivity of the composite restriction functor is found by a deep search.
/-- The sectionwise identity for iterated restriction, on complexes.
Source: Stacks 03DH (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def restrictionComp {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max u r})
    {X Y : C} (f : X ⟶ Y) :
    (SheafOfModules.overFunctor.{max u r} (ring R) X).mapHomologicalComplex (.up ℤ) ≅
      (SheafOfModules.overFunctor.{max u r} (ring R) Y).mapHomologicalComplex (.up ℤ) ⋙
        (SheafOfModules.overMap.{max u r} (ring R) f).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex
    (SheafOfModules.overFunctorMap.{max u r} (ring R) f).symm (.up ℤ)

universe d vd wd

/-- Compatibility of iterated derived restriction with the termwise product comparison.
Source: Stacks 03DH and 08DG (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def CompositionNormalization
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    {D : Type d} [Category.{vd} D] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B] [HasDerivedCategory.{wd} D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    {f : DerivedCategory A ⥤ DerivedCategory B}
    {g : DerivedCategory B ⥤ DerivedCategory D}
    {h : DerivedCategory A ⥤ DerivedCategory D}
    (qF : DerivedCategory.Q ⋙ f ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qG : DerivedCategory.Q ⋙ g ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qH : DerivedCategory.Q ⋙ h ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : h ≅ f ⋙ g)
    (t : H.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ M : CochainComplex A ℤ,
    c.hom.app (DerivedCategory.Q.obj M) ≫ g.map (qF.hom.app M) ≫
      qG.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
        qH.hom.app M ≫ DerivedCategory.Q.map (t.hom.app M)

universe q0 qU qV qW v0 vU vV vW

/-- The natural comparison isomorphisms and their canonical mate equations.
Source: Stacks 08DG and 03CE (blueprint: lem-sp-subterminal-derived-image-calculus).
This auxiliary record lists exactly the comparison and overlap assertions of the node.
The six final laws are the two unit identities, two cross identities and two W identities. -/
structure Comparisons
    {D0 : Type q0} [Category.{v0} D0] {DU : Type qU} [Category.{vU} DU]
    {DV : Type qV} [Category.{vV} DV] {DW : Type qW} [Category.{vW} DW]
    {rU : D0 ⥤ DU} {rV : D0 ⥤ DV} {rW : D0 ⥤ DW}
    {kU : DU ⥤ DW} {kV : DV ⥤ DW}
    {RU : DU ⥤ D0} {RV : DV ⥤ D0} {RW : DW ⥤ D0}
    {KU : DW ⥤ DU} {KV : DW ⥤ DV}
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (adjKU : kU ⊣ KU) (adjKV : kV ⊣ KV)
    (cU : rW ≅ rU ⋙ kU) (cV : rW ≅ rV ⋙ kV) where
  eU : RU ⋙ rU ≅ 𝟭 _
  eV : RV ⋙ rV ≅ 𝟭 _
  eW : RW ⋙ rW ≅ 𝟭 _
  eUV : RV ⋙ rU ≅ kV ⋙ KU
  eVU : RU ⋙ rV ≅ kU ⋙ KV
  eUW : RW ⋙ rU ≅ KU
  eVW : RW ⋙ rV ≅ KV
  dU : KU ⋙ RU ≅ RW
  dV : KV ⋙ RV ≅ RW
  selfU : eU.hom = adjU.counit
  selfV : eV.hom = adjV.counit
  selfW : eW.hom = adjW.counit
  crossUV : ∀ B, eUV.hom.app B = adjKU.unit.app (rU.obj (RV.obj B)) ≫
      KU.map (cU.inv.app (RV.obj B) ≫
        cV.hom.app (RV.obj B) ≫ kV.map (adjV.counit.app B))
  crossVU : ∀ B, eVU.hom.app B = adjKV.unit.app (rV.obj (RU.obj B)) ≫
      KV.map (cV.inv.app (RU.obj B) ≫
        cU.hom.app (RU.obj B) ≫ kU.map (adjU.counit.app B))
  toUW : ∀ D, eUW.hom.app D = adjKU.unit.app (rU.obj (RW.obj D)) ≫
      KU.map (cU.inv.app (RW.obj D) ≫ adjW.counit.app D)
  compositeU : ∀ D, dU.hom.app D = adjW.homEquiv _ _
      (cU.hom.app (RU.obj (KU.obj D)) ≫
        kU.map (adjU.counit.app (KU.obj D)) ≫ adjKU.counit.app D)
  toVW : ∀ D, eVW.hom.app D = adjKV.unit.app (rV.obj (RW.obj D)) ≫
      KV.map (cV.inv.app (RW.obj D) ≫ adjW.counit.app D)
  compositeV : ∀ D, dV.hom.app D = adjW.homEquiv _ _
      (cV.hom.app (RV.obj (KV.obj D)) ≫
        kV.map (adjV.counit.app (KV.obj D)) ≫ adjKV.counit.app D)
  overlapUnitU : ∀ A, rU.map (overlap adjU adjW cU A) ≫
      eUW.hom.app (kU.obj A) = eU.hom.app A ≫ adjKU.unit.app A
  overlapCrossU : ∀ B, rU.map (overlap adjV adjW cV B) ≫
      eUW.hom.app (kV.obj B) = eUV.hom.app B
  overlapWU : ∀ A, rW.map (overlap adjU adjW cU A) ≫
      eW.hom.app (kU.obj A) = cU.hom.app (RU.obj A) ≫ kU.map (eU.hom.app A)
  overlapUnitV : ∀ A, rV.map (overlap adjV adjW cV A) ≫
      eVW.hom.app (kV.obj A) = eV.hom.app A ≫ adjKV.unit.app A
  overlapCrossV : ∀ B, rV.map (overlap adjU adjW cU B) ≫
      eVW.hom.app (kU.obj B) = eVU.hom.app B
  overlapWV : ∀ A, rW.map (overlap adjV adjW cV A) ≫
      eW.hom.app (kV.obj A) = cV.hom.app (RV.obj A) ≫ kV.map (eV.hom.app A)

universe e ve we t vt
open CategoryTheory.Abelian Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section SitePairs
end SitePairs

section PairLaws
variable {A : Type a} [Category.{va} A] [Abelian A]
  {B : Type b} [Category.{vb} B] [Abelian B]
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  {ordinary : F ⊣ G} (p : DerivedPair F G ordinary)

end PairLaws

section Underived

end Underived

section Formal
section Formal
variable {A : Type a} [Category.{va} A]
  {B : Type b} [Category.{vb} B] {D : Type d} [Category.{vd} D]
  {f : A ⥤ B} {h : A ⥤ D} {k : D ⥤ A}
  {q : B ⥤ D} {Q : D ⥤ B}
  (adjW : h ⊣ k) (adjK : q ⊣ Q) (c : h ≅ f ⋙ q)

private def restrictionMate : k ⋙ f ⟶ Q where
  app X := adjK.homEquiv _ _ (c.inv.app (k.obj X) ≫ adjW.counit.app X)
  naturality := by
    intro X Y a
    change f.map (k.map a) ≫ adjK.homEquiv _ _ _ =
      adjK.homEquiv _ _ _ ≫ Q.map a
    rw [← adjK.homEquiv_naturality_left, ← adjK.homEquiv_naturality_right]
    congr 1
    change q.map (f.map (k.map a)) ≫ (c.inv.app (k.obj Y) ≫
      adjW.counit.app Y) = (c.inv.app (k.obj X) ≫ adjW.counit.app X) ≫ a
    have hc := c.inv.naturality (k.map a)
    dsimp only [Functor.comp_map] at hc
    rw [← Category.assoc, hc, Category.assoc]
    erw [adjW.counit.naturality]
    simp only [Functor.id_map, Category.assoc]

end Formal

section BuildComparisons
variable
    {D0 : Type q0} [Category.{v0} D0] {DU : Type qU} [Category.{vU} DU]
    {DV : Type qV} [Category.{vV} DV] {DW : Type qW} [Category.{vW} DW]
    {rU : D0 ⥤ DU} {rV : D0 ⥤ DV} {rW : D0 ⥤ DW}
    {kU : DU ⥤ DW} {kV : DV ⥤ DW}
    {RU : DU ⥤ D0} {RV : DV ⥤ D0} {RW : DW ⥤ D0}
    {KU : DW ⥤ DU} {KV : DW ⥤ DV}
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (adjKU : kU ⊣ KU) (adjKV : kV ⊣ KV)
    (cU : rW ≅ rU ⋙ kU) (cV : rW ≅ rV ⋙ kV)

end BuildComparisons

end Formal

section Composition
section
variable {A : Type a} [Category.{va} A] [Abelian A]
  {B : Type b} [Category.{vb} B] [Abelian B]
  {E : Type e} [Category.{ve} E] [Abelian E]
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{we} E]
  (F : A ⥤ B) (G : B ⥤ E) (H : A ⥤ E)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private def exactComposition (t : H ≅ F ⋙ G) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  (Functor.exactDerivedRestrictionComposition F G H t.symm).symm

end

end Composition

section LiftOverlap
section
variable {A : Type a} [Category.{va} A] [Abelian A]
  {B : Type b} [Category.{vb} B] [Abelian B]
  {D : Type d} [Category.{vd} D] [Abelian D]
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{wd} D]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  {H : A ⥤ D} {K : D ⥤ A} [H.Additive] [K.Additive]
  {adjF : F ⊣ G} {adjH : H ⊣ K}
  (p : DerivedPair F G adjF) (s : DerivedPair H K adjH)
  (T : B ⥤ D) [T.Additive]
  (Td : DerivedCategory B ⥤ DerivedCategory D)
  (qT : DerivedCategory.Q ⋙ Td ≅ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (c : s.left ≅ p.left ⋙ Td)
  (t : H.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ))
  (hc : CompositionNormalization p.qF qT s.qF c t)

end

end LiftOverlap

section OrdinaryOverlap
end OrdinaryOverlap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w0 wU wV wW

end CategoryTheory.SubterminalImageCalculus
