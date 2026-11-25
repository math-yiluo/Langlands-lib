/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom

/-!
# Sheafified sectionwise localization on a ringed site

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- Sectionwise carrier of the localization, using Mathlib's actual ring localization.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
abbrev ringedSectionLocalizationCarrier
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :=
  Localization.Away (M := O.obj.obj X) (s.val X)

/-- The image of a global section is invertible after localization on the target object.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: naturality identifies the restricted section with the target section, whose image
in its localization is a unit by `IsLocalization.Away.algebraMap_isUnit`. -/
theorem ringedSectionLocalization_isUnit
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    IsUnit ((algebraMap (O.obj.obj Y) (ringedSectionLocalizationCarrier O s Y))
      (O.obj.map a ((s.val X : O.obj.obj X)))) := by
  have hs : O.obj.map a (s.val X) = s.val Y := s.property a
  rw [hs]
  exact IsLocalization.Away.algebraMap_isUnit (R := O.obj.obj Y)
    (S := ringedSectionLocalizationCarrier O s Y) (s.val Y)

/-- Restriction on sectionwise localizations, given by the localization universal property.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedSectionLocalizationMap
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    ringedSectionLocalizationCarrier O s X →+* ringedSectionLocalizationCarrier O s Y :=
  IsLocalization.Away.lift (R := O.obj.obj X) (s.val X)
    (g := (algebraMap (O.obj.obj Y) (ringedSectionLocalizationCarrier O s Y)).comp
      (O.obj.map a).hom)
    (ringedSectionLocalization_isUnit O s a)

/-- Localization restriction is semilinear over restriction of coefficients.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: the localization lift extends the restriction ring homomorphism; apply
multiplicativity to the scalar action defined by the algebra map. -/
theorem ringedSectionLocalizationMap_smul
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y)
    (r : O.obj.obj X) (x : ringedSectionLocalizationCarrier O s X) :
    ringedSectionLocalizationMap O s a (r • x) =
      O.obj.map a r • ringedSectionLocalizationMap O s a x := by
  simp only [Algebra.smul_def, map_mul, ringedSectionLocalizationMap,
    IsLocalization.Away.lift_eq, RingHom.comp_apply]

/-- The linear form of localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedSectionLocalizationLinearMap
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrier O s X) ⟶
      (ModuleCat.restrictScalars (O.obj.map a).hom).obj
        (ModuleCat.of (O.obj.obj Y) (ringedSectionLocalizationCarrier O s Y)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrier O s X))
    (Y := (ModuleCat.restrictScalars (O.obj.map a).hom).obj
      (ModuleCat.of (O.obj.obj Y) (ringedSectionLocalizationCarrier O s Y)))
    { toFun := ringedSectionLocalizationMap O s a
      map_add' := (ringedSectionLocalizationMap O s a).map_add
      map_smul' := ringedSectionLocalizationMap_smul O s a }

/-- Identity compatibility of sectionwise localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: both sides extend the identity ring map, so localization uniqueness identifies them. -/
theorem ringedSectionLocalizationLinearMap_id
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    ringedSectionLocalizationLinearMap O s (𝟙 X) =
      (ModuleCat.restrictScalarsId' (O.obj.map (𝟙 X)).hom
        (congrArg CommRingCat.Hom.hom (O.obj.map_id X))).inv.app _ := by
  have h : ringedSectionLocalizationMap O s (𝟙 X) =
      RingHom.id (ringedSectionLocalizationCarrier O s X) := by
    apply IsLocalization.ringHom_ext (R := O.obj.obj X)
      (Submonoid.powers (s.val X))
    ext r
    simp [ringedSectionLocalizationMap]
  ext x
  change ringedSectionLocalizationMap O s (𝟙 X) x = x
  exact DFunLike.congr_fun h x

/-- Composition compatibility of sectionwise localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: both maps extend the composite restriction on the coefficient ring; uniqueness
of localization lifts identifies them, including the restriction-of-scalars comparison. -/
theorem ringedSectionLocalizationLinearMap_comp
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y Z : Cᵒᵖ}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    ringedSectionLocalizationLinearMap O s (a ≫ b) =
      ringedSectionLocalizationLinearMap O s a ≫
        (ModuleCat.restrictScalars (O.obj.map a).hom).map
          (ringedSectionLocalizationLinearMap O s b) ≫
        (ModuleCat.restrictScalarsComp' (O.obj.map a).hom (O.obj.map b).hom
          (O.obj.map (a ≫ b)).hom
          (congrArg CommRingCat.Hom.hom (O.obj.map_comp a b))).inv.app _ := by
  have h : ringedSectionLocalizationMap O s (a ≫ b) =
      (ringedSectionLocalizationMap O s b).comp (ringedSectionLocalizationMap O s a) := by
    apply IsLocalization.ringHom_ext (R := O.obj.obj X)
      (Submonoid.powers (s.val X))
    ext r
    simp [ringedSectionLocalizationMap, Functor.map_comp]
  ext x
  change ringedSectionLocalizationMap O s (a ≫ b) x =
    ringedSectionLocalizationMap O s b (ringedSectionLocalizationMap O s a x)
  exact DFunLike.congr_fun h x

/-- The presheaf of modules `V ↦ O(V)[1/s(V)]`, with the actual localization lifts
as its restriction maps.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(auxiliary; not a blueprint node). -/
def ringedSectionLocalizationPresheaf
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj where
  obj X := ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrier O s X)
  map a := ringedSectionLocalizationLinearMap O s a
  map_id X := ringedSectionLocalizationLinearMap_id O s X
  map_comp a b := ringedSectionLocalizationLinearMap_comp O s a b

/-- Localization of the ring sheaf as a module sheaf, obtained by sheafifying the
sectionwise localization presheaf.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(auxiliary; not a blueprint node). -/
def ringedSectionLocalization
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  (PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).obj
      (ringedSectionLocalizationPresheaf O s)

/-- The sectionwise units form a section of the localization presheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node).
Proof: the restriction maps are ring homomorphisms and therefore preserve one. -/
theorem ringedSectionLocalizationPresheaf_one_natural
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    (ringedSectionLocalizationPresheaf O s).map a
      (1 : ringedSectionLocalizationCarrier O s X) =
        (1 : ringedSectionLocalizationCarrier O s Y) := by
  exact (ringedSectionLocalizationMap O s a).map_one

/-- The canonical map from the ring sheaf to its localization as a module sheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(auxiliary; not a blueprint node). -/
def ringedSectionLocalizationUnit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalization O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    ((ringedSectionLocalizationPresheaf O s).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk
        (fun X ↦ (1 : ringedSectionLocalizationCarrier O s X))
        (fun {_ _} a ↦ ringedSectionLocalizationPresheaf_one_natural O s a)) ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
          (ringedSectionLocalizationPresheaf O s))

/-- Restricting a section on U gives a natural family on its slice.
Source: Stacks Project, algebraization.tex, Tag 099E
(auxiliary; not a blueprint node).
Proof: the commuting triangle defining a morphism in the slice and functoriality of the
ring presheaf identify both composite restrictions. -/
theorem ringedSliceSection_natural (U : C) (f : O.obj.obj (op U))
    {X Y : (Over U)ᵒᵖ} (a : X ⟶ Y) :
    (O.over U).obj.map a (O.obj.map (unop X).hom.op f) =
      O.obj.map (unop Y).hom.op f := by
  change (O.obj.map (unop X).hom.op ≫ O.obj.map a.unop.left.op) f = _
  rw [← O.obj.map_comp, ← op_comp, Over.w a.unop]

/-- A section over U, viewed as a global section on the slice site.
Source: Stacks Project, algebraization.tex, Tag 099E
(auxiliary; not a blueprint node). -/
def ringedSliceSection (U : C) (f : O.obj.obj (op U)) :
    ((O.over U).obj ⋙ forget CommRingCat).sections where
  val X := O.obj.map (unop X).hom.op f
  property a := ringedSliceSection_natural O U f a

end CategoryTheory
