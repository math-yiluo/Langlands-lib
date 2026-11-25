/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement

import WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Data.ZMod.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Cartier reduction and site comparison
Source: blueprint main-20261015, Cartier comparison proof
(blueprint: lem-sp-cartier-reduction-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify AlgebraicGeometry.cartierEtaleAbHasExt
  AlgebraicGeometry.ProEtale.geoCartierIntegralExt AlgebraicGeometry.Etale.hasExt_sheaf_moduleCat
  AlgebraicGeometry.ProEtale.geoCartierModuleExt
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] comparisonUpperStar cartierUnitsComparison
  cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit
  cartierProIntegralGenerator cartierProRootMap cartierReducedEtale cartierReducedPro
  CartierEtaleReductionSpec CartierProReductionSpec cartierResidueReducedPro

/-- For a closed immersion i:D→Z and n>0, the normalized supported integral generator
i_*Z_D→forget(i_*(ULift(Z/n))_D) on the pro-etale site has the unbounded DerivedUnit property
[def-sfb-cartier-reduction-data, def-sp-exact-functor-derived-unit].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-cartier-pro-integral-residue-derived-unit).
Proof: Pull the supported etale integer/residue short exact sequence back by exact comparison.
Transport its two integral terms by the canonical supported integral comparison and its residue term
by the coefficient-forgetting comparison followed by the supported residue comparison. All are
isomorphisms. The defining formula for the pro integral generator identifies the transported
quotient map. Thus the sequence nF→F→forget(i_*R_D) is short exact. Apply the site-general
quotient-derived-unit theorem directly on the pro-etale site. -/
theorem pro_integral_residue_derived_unit (n : ℕ) (hn : 0 < n)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    (cartierForget (ULift.{u + 1} (ZMod n)) Z).DerivedUnit
      ((lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) i).obj
        (geoCartierConstant (ULift.{u + 1} (ZMod n)) D))
      (cartierProIntegralGenerator (ULift.{u + 1} (ZMod n)) i) := by
  let R := ULift.{u + 1} (ZMod n)
  let : NeZero n := ⟨hn.ne'⟩
  let F := comparisonUpperStar AddCommGrpCat.{u + 1} Z
  let η := Etale.supportedIntegralGenerator R i
  obtain ⟨w, hw⟩ := Etale.supported_integral_residue_sequence i n hn
  let S := ShortComplex.mk (n • 𝟙 _) η w
  let a := cartierIntegralSourceIso i
  have : IsIso (geoCartierSourceComparison R i) := cartierSourceComparison_isIso R i
  let b := (forgetComparisonIso R Z).app
      ((Etale.lowerStar (ModuleCat.{u + 1} R) i).obj (Etale.ordinaryFiniteConstant R D)) ≪≫
    (cartierForget R Z).mapIso (asIso (geoCartierSourceComparison R i))
  have hb : b.hom = cartierForgetComparison R Z
      ((Etale.lowerStar (ModuleCat.{u + 1} R) i).obj (Etale.ordinaryFiniteConstant R D)) ≫
        (cartierForget R Z).map (geoCartierSourceComparison R i) := by
    dsimp only [b, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom]
    rw [forgetComparisonIso_hom]
    rfl
  have hgen : cartierProIntegralGenerator R i = a.inv ≫ F.map η ≫ b.hom := by
    rw [hb]
    unfold cartierProIntegralGenerator
    rfl
  have wp : (n • 𝟙 _) ≫ cartierProIntegralGenerator R i = 0 := by
    rw [hgen]
    calc
      (n • 𝟙 _) ≫ (a.inv ≫ F.map η ≫ b.hom) =
          a.inv ≫ (F.map (n • 𝟙 _) ≫ F.map η) ≫ b.hom := by
        simp only [F.map_nsmul, F.map_id, Preadditive.nsmul_comp,
          Preadditive.comp_nsmul, Category.id_comp, Category.assoc]
        simp only [← Category.assoc]
        erw [Category.comp_id]
      _ = 0 := by rw [← F.map_comp, w, F.map_zero, zero_comp, comp_zero]
  let S' := ShortComplex.mk (n • 𝟙 _) (cartierProIntegralGenerator R i) wp
  let e : S.map F ≅ S' := by
    refine ShortComplex.isoMk a a b ?_ ?_
    · change a.hom ≫ (n • 𝟙 _) = F.map (n • 𝟙 _) ≫ a.hom
      simp only [F.map_nsmul, F.map_id, Preadditive.nsmul_comp,
        Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
    · change a.hom ≫ cartierProIntegralGenerator R i = F.map η ≫ b.hom
      rw [hgen]
      simp only [Iso.hom_inv_id_assoc]
  have hS' := ShortComplex.shortExact_of_iso e (hw.map_of_exact F)
  exact CategoryTheory.Sheaf.ConstantResidue.quotient_derived_unit
    (Scheme.ProEt.topology Z) n hn _ _ (cartierProIntegralGenerator R i) wp hS'
end AlgebraicGeometry.ProEtale
