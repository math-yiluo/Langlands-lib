/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionSlicesSupplement
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionSheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.CategoryTheory.Ringed.RingedPrincipalLocalTests
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.Algebra.Homology.PrincipalConeTower
import WeilConjectures.CategoryTheory.Native.NativePrincipalCompletenessSmallModel
import WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import WeilConjectures.CategoryTheory.Principal.PrincipalConeSmallSiteCriterion
/-! # Principal cone criterion with independent site and coefficient sizes

Source: Stacks 03A0, 03CH, 03DA, 03DG, 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-native-principal-cone-criterion). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxErrors 5
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
set_option hygiene false in
local notation "F" => AsSmall.down.{v, c, max c v r} (C := C)
set_option hygiene false in
local notation "Jsmall" => (F).inducedTopology J
variable [(F).IsEquivalence]
variable (R : Sheaf J CommRingCat.{max c v r})
set_option hygiene false in
local notation "S" => restrictedCommRing.{max c v r, c, max c v r, v, r} (K := Jsmall) F R
set_option hygiene false in
local notation "Rg" => NativeRings.{max c v r, c, v} R
set_option hygiene false in
local notation "Rs" => NativeRings.{max c v r, max c v r, max c v r} S
variable
  [HasSheafify J AddCommGrpCat.{max c v r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify Jsmall AddCommGrpCat.{max c v r}] [(Jsmall).WEqualsLocallyBijective
    AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, HasSheafify ((Jsmall).over U) AddCommGrpCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, ((Jsmall).over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, HasSheafify ((Jsmall).over U) CommRingCat.{max c v r}]
  [HasDerivedCategory.{w} (NativeModules.{max c v r, c, v} R)]
  [HasDerivedCategory.{w} (NativeModules.{max c v r, max c v r, max c v r} S)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rg).over U))]
  [∀ U : AsSmall.{max c v r} C, HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rs).over U))]
attribute [local instance] sliceDense globalModulesEquivalence sliceModulesEquivalence

variable [HasCountableProducts (NativeModules.{max c v r, c, v} R)]
  [HasCountableProducts (NativeModules.{max c v r, max c v r, max c v r} S)]
  [HasExactLimitsOfShape (Discrete ℕ)
    (NativeModules.{max c v r, max c v r, max c v r} S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ NativeModules.{max c v r, max c v r, max c v r} S)]

attribute [local irreducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit

/-- The principal cone completion satisfies the local criterion before shrinking the site. Restrict
the complex and scalar to AsSmall and apply the small-site criterion. The additive-equivalence
comparison identifies its cone completion and its specified unit with the restriction of the
native ones. Transfer local completeness by the small-model equivalence. For the unit criterion
use the derived comparison square, cancel its two isomorphisms, and reflect invertibility
through the derived equivalence.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-native-principal-cone-criterion). -/
theorem nativePrincipalConeCriterion
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (P : CochainComplex (NativeModules.{max c v r, c, v} R) ℤ) (μ : End P)
    (hμ : ∀ (q : ℤ) (U : Cᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x =
        @SMul.smul _ _ ((P.X q).val.obj U).isModule.toSMul (a.val U) x) :
    principalLocallyComplete.{c, v, r, w} R a
        (DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion μ)) ∧
      (principalLocallyComplete.{c, v, r, w} R a (DerivedCategory.Q.obj P) ↔
        IsIso (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ))) := by
  let H := restrictModules.{max c v r, c, max c v r, v, r} (K := Jsmall) F R
  let : H.IsEquivalence :=
    globalModulesEquivalence.{max c v r, c, max c v r, v, r} (K := Jsmall) F R
  let G := H.mapHomologicalComplex (.up ℤ)
  let μ' := End.of (G.map μ.asHom)
  let a' := restrictedSection.{max c v r, c, max c v r, v, r} (K := Jsmall) F R a
  have hμ' : ∀ (q : ℤ) (U : (AsSmall.{max c v r} C)ᵒᵖ)
      (x : ((G.obj P).X q).val.obj U),
      (μ'.asHom.f q).val.app U x =
        @SMul.smul _ _ (((G.obj P).X q).val.obj U).isModule.toSMul (a'.val U)
        x := by
    intro q U x
    exact hμ q ((F).op.obj U) x
  obtain ⟨hc, hi⟩ := principalConeSmallSiteCriterion S a' (G.obj P) μ' hμ'
  obtain ⟨c, hcunit⟩ := CochainComplex.principalCompletionMap H μ
  let d := H.mapDerivedCategoryFactors.app (CochainComplex.PrincipalCone.completion μ) ≪≫
    DerivedCategory.Q.mapIso c
  let b := H.mapDerivedCategoryFactors.app P
  have hunit : H.mapDerivedCategory.map
      (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ)) ≫ d.hom =
      b.hom ≫ DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ') := by
    change _ ≫ (H.mapDerivedCategoryFactors.app _).hom ≫ DerivedCategory.Q.map c.hom = _
    simp only [Iso.app_hom]
    rw [← Category.assoc, H.mapDerivedCategoryFactors_hom_naturality,
      Category.assoc, ← Functor.map_comp, hcunit]
    rfl
  refine ⟨?_, ?_⟩
  · apply (smallModelComplete.{c, v, r, w} R a _).mpr
    exact (principalLocallyComplete_iso.{max c v r, max c v r, r, w} S a' d).mpr hc
  · refine (smallModelComplete.{c, v, r, w} R a _).trans ?_
    refine (principalLocallyComplete_iso.{max c v r, max c v r, r, w} S a' b).trans ?_
    refine hi.trans ?_
    have hiff : IsIso (H.mapDerivedCategory.map
        (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ))) ↔
        IsIso (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ')) := by
      rw [← isIso_comp_right_iff _ d.hom, hunit, isIso_comp_left_iff]
    exact hiff.symm.trans (isIso_iff_of_reflects_iso _ _)
end CategoryTheory.NativeRestriction
