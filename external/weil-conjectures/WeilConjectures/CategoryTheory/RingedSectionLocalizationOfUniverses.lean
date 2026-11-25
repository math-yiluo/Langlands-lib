/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.Ring.Adjunctions

/-!
# Section localization with independent site universes

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(auxiliary; not a blueprint node).
The construction is the same sectionwise localization followed by sheafification.
This interface allows a site with different object and morphism universes. Sheafification
is parameterized by its existing instances in the chosen coefficient universe. The previous
small-category interface is retained by the public import.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uC vC

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (O : Sheaf J CommRingCat.{u})

/-- Sectionwise carrier of the localization, using Mathlib's actual ring localization.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
abbrev ringedSectionLocalizationCarrierOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :=
  Localization.Away (M := O.obj.obj X) (s.val X)

set_option linter.unusedSectionVars false in
/-- The image of a global section is invertible after localization on the target object.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: naturality identifies the restricted section with the target section, whose image
in its localization is a unit by `IsLocalization.Away.algebraMap_isUnit`. -/
theorem ringedSectionLocalization_isUnitOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    IsUnit ((algebraMap (O.obj.obj Y) (ringedSectionLocalizationCarrierOfUniverses O s Y))
      (O.obj.map a ((s.val X : O.obj.obj X)))) := by
  have hs : O.obj.map a (s.val X) = s.val Y := s.property a
  rw [hs]
  exact IsLocalization.Away.algebraMap_isUnit (R := O.obj.obj Y)
    (S := ringedSectionLocalizationCarrierOfUniverses O s Y) (s.val Y)

/-- Restriction on sectionwise localizations, given by the localization universal property.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedSectionLocalizationMapOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    ringedSectionLocalizationCarrierOfUniverses O s X →+*
      ringedSectionLocalizationCarrierOfUniverses O s Y :=
  IsLocalization.Away.lift (R := O.obj.obj X) (s.val X)
    (g := (algebraMap (O.obj.obj Y) (ringedSectionLocalizationCarrierOfUniverses O s Y)).comp
      (O.obj.map a).hom)
    (ringedSectionLocalization_isUnitOfUniverses O s a)

/-- Localization restriction is semilinear over restriction of coefficients.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: the localization lift extends the restriction ring homomorphism; apply
multiplicativity to the scalar action defined by the algebra map. -/
theorem ringedSectionLocalizationMap_smulOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y)
    (r : O.obj.obj X) (x : ringedSectionLocalizationCarrierOfUniverses O s X) :
    ringedSectionLocalizationMapOfUniverses O s a (r • x) =
      O.obj.map a r • ringedSectionLocalizationMapOfUniverses O s a x := by
  simp only [Algebra.smul_def, map_mul, ringedSectionLocalizationMapOfUniverses,
    IsLocalization.Away.lift_eq, RingHom.comp_apply]

/-- The linear form of localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedSectionLocalizationLinearMapOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X) ⟶
      (ModuleCat.restrictScalars (O.obj.map a).hom).obj
        (ModuleCat.of (O.obj.obj Y) (ringedSectionLocalizationCarrierOfUniverses O s Y)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X))
    (Y := (ModuleCat.restrictScalars (O.obj.map a).hom).obj
      (ModuleCat.of (O.obj.obj Y) (ringedSectionLocalizationCarrierOfUniverses O s Y)))
    { toFun := ringedSectionLocalizationMapOfUniverses O s a
      map_add' := (ringedSectionLocalizationMapOfUniverses O s a).map_add
      map_smul' := ringedSectionLocalizationMap_smulOfUniverses O s a }

/-- Identity compatibility of sectionwise localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: both sides extend the identity ring map, so localization uniqueness identifies them. -/
theorem ringedSectionLocalizationLinearMap_idOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    ringedSectionLocalizationLinearMapOfUniverses O s (𝟙 X) =
      (ModuleCat.restrictScalarsId' (O.obj.map (𝟙 X)).hom
        (congrArg CommRingCat.Hom.hom (O.obj.map_id X))).inv.app _ := by
  have h : ringedSectionLocalizationMapOfUniverses O s (𝟙 X) =
      RingHom.id (ringedSectionLocalizationCarrierOfUniverses O s X) := by
    apply IsLocalization.ringHom_ext (R := O.obj.obj X)
      (Submonoid.powers (s.val X))
    ext r
    simp [ringedSectionLocalizationMapOfUniverses]
  ext x
  change ringedSectionLocalizationMapOfUniverses O s (𝟙 X) x = x
  exact DFunLike.congr_fun h x

/-- Composition compatibility of sectionwise localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: both maps extend the composite restriction on the coefficient ring; uniqueness
of localization lifts identifies them, including the restriction-of-scalars comparison. -/
theorem ringedSectionLocalizationLinearMap_compOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y Z : Cᵒᵖ}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    ringedSectionLocalizationLinearMapOfUniverses O s (a ≫ b) =
      ringedSectionLocalizationLinearMapOfUniverses O s a ≫
        (ModuleCat.restrictScalars (O.obj.map a).hom).map
          (ringedSectionLocalizationLinearMapOfUniverses O s b) ≫
        (ModuleCat.restrictScalarsComp' (O.obj.map a).hom (O.obj.map b).hom
          (O.obj.map (a ≫ b)).hom
          (congrArg CommRingCat.Hom.hom (O.obj.map_comp a b))).inv.app _ := by
  have h : ringedSectionLocalizationMapOfUniverses O s (a ≫ b) =
      (ringedSectionLocalizationMapOfUniverses O s b).comp
        (ringedSectionLocalizationMapOfUniverses O s a) := by
    apply IsLocalization.ringHom_ext (R := O.obj.obj X)
      (Submonoid.powers (s.val X))
    ext r
    simp [ringedSectionLocalizationMapOfUniverses, Functor.map_comp]
  ext x
  change ringedSectionLocalizationMapOfUniverses O s (a ≫ b) x =
    ringedSectionLocalizationMapOfUniverses O s b (ringedSectionLocalizationMapOfUniverses O s a x)
  exact DFunLike.congr_fun h x

/-- The presheaf of modules `V ↦ O(V)[1/s(V)]`, with the actual localization lifts
as its restriction maps.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(auxiliary; not a blueprint node). -/
def ringedSectionLocalizationPresheafOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj where
  obj X := ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X)
  map a := ringedSectionLocalizationLinearMapOfUniverses O s a
  map_id X := ringedSectionLocalizationLinearMap_idOfUniverses O s X
  map_comp a b := ringedSectionLocalizationLinearMap_compOfUniverses O s a b

/-- Localization of the ring sheaf as a module sheaf, obtained by sheafifying the
sectionwise localization presheaf.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(auxiliary; not a blueprint node). -/
def ringedSectionLocalizationOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  (PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).obj
      (ringedSectionLocalizationPresheafOfUniverses O s)

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (s : (R.obj ⋙ forget CommRingCat).sections)

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

/- The additive sheafification has a canonical multiplication: multiply local representatives
and glue. Local injectivity makes the product independent of the representatives. The ring laws
and the compatibility of lifts are checked on covering sieves. This realizes the sheafification
argument in the comparison theorem below without identifying the site and coefficient universes. -/
namespace RingedLocalizationComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {P : Cᵒᵖ ⥤ CommRingCat.{u}} {A : Sheaf J AddCommGrpCat.{u}}
variable (η : (P ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶ A.obj)
variable [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]

private lemma ext {X : Cᵒᵖ} {x y : A.obj.obj X} (S : Sieve X.unop) (hS : S ∈ J X.unop)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop), S g → A.obj.map g.op x = A.obj.map g.op y) :
    x = y :=
  A.isSeparated _ _ hS x y (fun _ g hg ↦ h g hg)

variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private lemma comparison {B : Sheaf J RingCat.{u}}
    (P : PresheafOfModules.{u} B.obj) (A : SheafOfModules.{u} B)
    (φ : P ⟶ A.val)
    [PresheafOfModules.IsLocallyInjective J φ]
    [PresheafOfModules.IsLocallySurjective J φ] :
    ∃ e : A ≅ (PresheafOfModules.sheafification (𝟙 B.obj)).obj P,
      φ ≫ e.hom.val = (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P := by
  let S := (PresheafOfModules.sheafification (𝟙 B.obj)).obj P
  let η : P ⟶ S.val := (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P
  let g : S ⟶ A := (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).symm φ
  have hg : η ≫ g.val = φ := by
    exact (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).apply_symm_apply φ
  let f : A ⟶ S := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
    (f := φ) S.isSheaf).symm η⟩
  have hf : φ ≫ f.val = η := by
    exact (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := φ) S.isSheaf).apply_symm_apply η
  have hfg : f ≫ g = 𝟙 A := by
    apply (SheafOfModules.fullyFaithfulForget _).map_injective
    apply (PresheafOfModules.homEquivOfIsLocallyBijective (f := φ) A.isSheaf).injective
    change φ ≫ (f.val ≫ g.val) = φ ≫ 𝟙 A.val
    rw [← Category.assoc, hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 S := by
    apply (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).injective
    change η ≫ (g.val ≫ f.val) = η ≫ 𝟙 S.val
    rw [← Category.assoc, hg, hf, Category.comp_id]
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end RingedLocalizationComparison

end

end CategoryTheory
