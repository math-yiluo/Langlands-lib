/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Sites.ConstantResidue.ResidueKummerDerivedUnit
public import WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
public import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
public import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Kummer-normalized derived residue units
(blueprint: lem-sp-residue-kummer-derived-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u wAb wMod wE
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped ZeroObject
namespace CategoryTheory.Sheaf.ConstantResidue
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{u + 1}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [EssentiallySmall.{u + 1} C] [HasTerminal C]

/-- In the site and derived-category setting of residue Kummer reduction
[lem-sp-residue-kummer-derived-unit], suppose 0→K→G→G→0 has last map n>0 and f:K≅UH for a
ULift(Z/n)-module sheaf H. Then the connecting class followed by mk0(f) is a degree-one derived Ext
unit [def-sp-derived-scalar-ext-unit].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-residue-kummer-iso-derived-unit).
Proof: Replace the kernel map by f inverse followed by the original inclusion. The resulting short
complex is isomorphic to the original one and is therefore short exact. Apply the residue Kummer
unit theorem to it. Naturality of Ext classes for the isomorphism of short exact sequences
identifies its class with the original connecting class followed by f. -/
theorem kummer_iso_derived_unit (n : ℕ) (hn : 0 < n)
    (K G : Sheaf J AddCommGrpCat.{u + 1})
    (H : Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    [HasDerivedCategory.{wAb} (Sheaf J AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{wMod}
      (Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))]
    [HasExt.{wE} (Sheaf J AddCommGrpCat.{u + 1})]
    [(sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).Additive]
    [PreservesFiniteLimits (sheafCompose J
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}))]
    [PreservesFiniteColimits (sheafCompose J
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}))]
    (i : K ⟶ G) (hi : i ≫ (n • 𝟙 G) = 0)
    (hK : (ShortComplex.mk i (n • 𝟙 G) hi).ShortExact)
    (f : K ≅ (sheafCompose J (forget₂
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})).obj H) :
    (sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).DerivedExtUnit G H 1
        (hK.extClass.comp (Ext.mk₀ f.hom) (add_zero 1)) := by
  let i' := f.inv ≫ i
  have hi' : i' ≫ (n • 𝟙 G) = 0 := by
    change (f.inv ≫ i) ≫ (n • 𝟙 G) = 0
    rw [Category.assoc, hi, comp_zero]
  let e : ShortComplex.mk i' (n • 𝟙 G) hi' ≅
      ShortComplex.mk i (n • 𝟙 G) hi :=
    ShortComplex.isoMk f.symm (Iso.refl _) (Iso.refl _) (by simp [i']) (by simp)
  have hK' := ShortComplex.shortExact_of_iso e.symm hK
  have hunit := kummer_derived_unit J n hn G H i' hi' hK'
  have he := ShortComplex.ShortExact.extClass_naturality hK' hK e.hom
  have hc : hK'.extClass = hK.extClass.comp (Ext.mk₀ f.hom) (add_zero 1) := by
    have hh := congrArg (fun z ↦ z.comp (Ext.mk₀ f.hom) (add_zero 1)) he
    simpa [e, Ext.mk₀_comp_mk₀_assoc] using hh
  rw [hc] at hunit
  exact hunit
end CategoryTheory.Sheaf.ConstantResidue
