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
import WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionLocalTest
import WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionDivisibility
/-! # Principal completeness on a small model

Source: Stacks 03A0, 03CH, 03DA, 03DG and 0999.
(blueprint: lem-pur-native-principal-completeness-small-model). -/

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

private theorem reflectZero {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (G : A ⥤ B)
    [G.Faithful] [G.PreservesZeroMorphisms] (X : A) (h : IsZero (G.obj X)) :
    IsZero X := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact G.zero_of_map_zero _ (by simpa using h)

/-- Principal local completeness is preserved and reflected on the AsSmall model. Every compatible
slice section is determined by its terminal value, hence is the restriction of a native slice
section. Transfer its covering divisibility and localization test. In the reverse direction
choose the AsSmall copy of each native object; the faithful derived slice equivalence reflects
zero objects. No vanishing or invertibility hypothesis on the generator is used.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 0999.
(blueprint: lem-pur-native-principal-completeness-small-model). -/
theorem smallModelComplete
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (N : DerivedCategory (NativeModules.{max c v r, c, v} R)) :
    letI := globalModulesEquivalence.{max c v r, c, max c v r, v, r}
      (K := Jsmall) F R
    principalLocallyComplete.{c, v, r, w} R a N ↔
      principalLocallyComplete.{max c v r, max c v r, r, w} S
        (restrictedSection.{max c v r, c, max c v r, v, r} (K := Jsmall) F R a)
        ((restrictModules.{max c v r, c, max c v r, v, r} (K := Jsmall) F
          R).mapDerivedCategory.obj N) := by
  let := globalModulesEquivalence.{max c v r, c, max c v r, v, r}
    (K := Jsmall) F R
  constructor
  · intro h U s hs
    let s₀ := principalSliceSection.{c, v, r} R ((F).obj U)
      (s.val (op (Over.mk (𝟙 U))))
    have he : s = restrictedSection.{max c v r, max c v, max c v r, v, r} (K := (Jsmall).over U)
        (Over.post F) (R.over ((F).obj U)) s₀ := by
      rw [principalSliceSection_eta.{max c v r, max c v r, r} S U s]
      rfl
    rw [he] at hs ⊢
    have hz := h ((F).obj U) s₀
      ((localDivisibilityRestriction.{max c v r, c, max c v r, v, r} (K := Jsmall) F R a U s₀).mpr
        hs)
    obtain ⟨e⟩ := localTestRestriction.{max c v r, c, max c v r, v, r, w} (K := Jsmall) F R U N s₀
    exact (Functor.map_isZero _ hz).of_iso e.symm
  · intro h U s hs
    let V := AsSmall.up.{v, c, max c v r}.obj U
    have hs' := (localDivisibilityRestriction.{max c v r, c, max c v r, v, r} (K := Jsmall) F R a
      V s).mp hs
    have hz := h V _ hs'
    obtain ⟨e⟩ := localTestRestriction.{max c v r, c, max c v r, v, r, w} (K := Jsmall) F R V N s
    exact reflectZero _ _ (hz.of_iso e)

end CategoryTheory.NativeRestriction
