/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Derived.DerivedScalarExtUnit
import WeilConjectures.CategoryTheory.Derived.DerivedScalarExtUnitTransport
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
import all WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Data.ZMod.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import all WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import all WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import all WeilConjectures.SixFunctors.BaseChange.DerivedForget
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all Mathlib.CategoryTheory.Abelian.ShortExact

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
attribute [local instance] HasDerivedCategory.standard HasExt.standard

open SheafOfModules.DivisibleReduction in
private theorem ringed_kummer_unit [EssentiallySmall.{u + 1} C] [HasTerminal C]
    (n : ℕ) (hn : 0 < n) (G : Integral J) (H : Residue J n)
    (i : (restriction J n).obj H ⟶ G) (wi : i ≫ (n • 𝟙 G) = 0)
    (hK : (ShortComplex.mk i (n • 𝟙 G) wi).ShortExact) :
    (restriction J n).DerivedExtUnit G H 1 (ShortComplex.ShortExact.extClass.{u + 2} hK) := by
  let S : ShortComplex (Integral J) :=
    ShortComplex.mk (𝟙 G) (0 : G ⟶ (0 : Integral J)) (by simp)
  have hS : S.ShortExact :=
    { exact := (S.exact_iff_epi rfl).2 (by dsimp [S]; infer_instance)
      mono_f := by dsimp [S]; infer_instance
      epi_g := (isZero_zero _).epi _ }
  let p : S.X₃ ⟶ (restriction J n).obj (0 : Residue J n) := 0
  have wp : (n • 𝟙 S.X₃) ≫ p = 0 := by simp [p]
  have hq : (ShortComplex.mk (n • 𝟙 S.X₃) p wp).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero _)
      mono_f := (isZero_zero _).mono _
      epi_g := ((restriction J n).map_isZero (isZero_zero _)).epi _ }
  let P : Presentation (J := J) n :=
    { S := S
      exact := hS
      H := H
      Q := 0
      i := i
      p := p
      wi := wi
      wp := wp
      kummer := hK
      quotient := hq }
  obtain ⟨D⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (projection J n)
  let I := identifications n D hn P
  let ad := SheafOfModules.sheafScalarDerivedAdjunction (projection J n) D
  unfold Functor.DerivedExtUnit
  intro K
  have h := (ad.homEquiv _ K).bijective.comp I.alphaB.symm.homFromEquiv.bijective
  have heq := I.kummer_unit
  change eta n D G ≫ (derivedRestriction n).map I.alphaB.hom = _ at heq
  convert h using 1
  ext f
  simp only [Function.comp_def, Iso.homFromEquiv_apply, Iso.symm_inv,
    Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  erw [hK.extClass_hom]
  have he := congrArg (fun z ↦ z ≫ (derivedRestriction n).map f) heq.symm
  dsimp only [kappa, P, S, eta, ad] at he
  simp only [Category.assoc] at he
  convert he using 1 <;> simp only [Category.assoc] <;> rfl

open SheafOfModules.DivisibleReduction in
/-- On an essentially small site with terminal object and the stated sheafification/exactness
hypotheses, let n>0 and H be a ULift(Z/n)-module sheaf. If 0→UH→G→G→0 is short exact, the last map
being n, its positive connecting class in Ext^1(G,UH) has the unbounded DerivedExtUnit property
[def-sp-derived-scalar-ext-unit].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-residue-kummer-derived-unit).
Proof: In integer modules use the split extension G→G→0 in normalized divisible-extension reduction.
Its Kummer identification identifies the derived adjunction unit with the positive connecting class.
Realize raw residue-module sheaves as constant-ring modules and abelian sheaves as integer modules.
Exact equivalences transport the universal property. Naturality of the short exact Ext class
identifies the transported connecting class without changing its sign. -/
theorem kummer_derived_unit [EssentiallySmall.{u + 1} C] [HasTerminal C]
    (n : ℕ) (hn : 0 < n)
    (G : Sheaf J AddCommGrpCat.{u + 1})
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
    (i : (sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).obj H ⟶ G)
    (hi : i ≫ (n • 𝟙 G) = 0)
    (hK : (ShortComplex.mk i (n • 𝟙 G) hi).ShortExact) :
    (sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).DerivedExtUnit G H 1
        (ShortComplex.ShortExact.extClass.{wE} hK) := by
  let R := ULift.{u + 1} (ZMod n)
  let TZ : Integral J ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
    SheafOfModules.toSheaf.{u + 1} (coefficientRing J (ULift.{u + 1} ℤ))
  have : TZ.IsEquivalence := integerForget_isEquivalence J
  have : PreservesFiniteLimits TZ := inferInstance
  have : PreservesFiniteColimits TZ := inferInstance
  let Gc : Integral J := TZ.asEquivalence.inverse.obj G
  let c : TZ.obj Gc ≅ G := TZ.asEquivalence.counitIso.app G
  let Q : Residue J n := (realize J R).obj H
  let d : TZ.obj ((restriction J n).obj Q) ≅ (forgetSheaf J R).obj H :=
    (realizeForgetIso J R).app H
  let ic : (restriction J n).obj Q ⟶ Gc := TZ.preimage (d.hom ≫ i ≫ c.inv)
  have hic : TZ.map ic = d.hom ≫ i ≫ c.inv := TZ.map_preimage _
  have wic : ic ≫ (n • 𝟙 Gc) = 0 := by
    apply TZ.map_injective
    rw [TZ.map_comp, TZ.map_nsmul, TZ.map_id, hic, TZ.map_zero]
    calc
      (d.hom ≫ i ≫ c.inv) ≫ (n • 𝟙 (TZ.obj Gc)) =
          d.hom ≫ (i ≫ (n • 𝟙 G)) ≫ c.inv := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.comp_id]
      _ = 0 := by rw [hi, zero_comp, comp_zero]
  let SK : ShortComplex (Integral J) := ShortComplex.mk ic (n • 𝟙 Gc) wic
  let SA : ShortComplex (Sheaf J AddCommGrpCat.{u + 1}) :=
    ShortComplex.mk i (n • 𝟙 G) hi
  let eK : SK.map TZ ≅ SA := by
    refine ShortComplex.isoMk d c c ?_ ?_
    · change d.hom ≫ i = TZ.map ic ≫ c.hom
      rw [hic]
      simp
    · change c.hom ≫ (n • 𝟙 G) = TZ.map (n • 𝟙 Gc) ≫ c.hom
      simp only [TZ.map_nsmul, TZ.map_id, Preadditive.nsmul_comp,
        Preadditive.comp_nsmul, Category.comp_id, Category.id_comp]
  have hKc : SK.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff TZ).1
      (ShortComplex.shortExact_of_iso eK.symm hK)
  have hunit := ringed_kummer_unit J n hn Gc Q ic wic hKc
  apply Functor.derivedExtUnit_transport (realize J R) (restriction J n) TZ
    (forgetSheaf J R) (realizeForgetIso J R) Gc H G c 1
    (ShortComplex.ShortExact.extClass.{u + 2} hKc) (ShortComplex.ShortExact.extClass.{wE} hK)
    ?_ hunit
  have he := ShortComplex.ShortExact.extClass_naturality
    (hKc.map_of_exact TZ) hK eK.hom
  rw [Ext.mapExactFunctor_extClass]
  simpa only [eK, ShortComplex.isoMk_hom_τ₁, ShortComplex.isoMk_hom_τ₃, d, Iso.app_hom] using he

end CategoryTheory.Sheaf.ConstantResidue
