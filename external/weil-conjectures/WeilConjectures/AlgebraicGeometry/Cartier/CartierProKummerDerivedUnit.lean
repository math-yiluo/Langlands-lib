/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.CategoryTheory.Scalar.ScalarExtUnitComposition
import WeilConjectures.CategoryTheory.Scalar.ScalarExtUnitIso
import WeilConjectures.CategoryTheory.Sites.ConstantResidue.ResidueKummerIsoDerivedUnit
import WeilConjectures.AlgebraicGeometry.Residue.ResidueFiniteRootMapIso
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProRootScalar
import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Adjunction.Unique

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

/-- Let n>0 be invertible on Z, R=ULift(Z/n), A a commutative ring killed by n, i:D→Z any scheme
morphism and φ:R→A. If two Cartier Ext classes have GeoCartierScalarCompatibility
[lemma-cycle-class-cartier-divisor], then the normalized full pro-etale Kummer class
G_m,pro→forget(A_Z(1))[1] is a degree-one scalar unit [def-sfb-cartier-reduction-data,
def-sp-derived-scalar-ext-unit]. Source: blueprint Cartier derived reduction and comparison
paragraphs; Stacks 0152, 06YY and 0GLZ (blueprint: lem-sp-cartier-pro-kummer-derived-unit).
Proof: The pro-etale residue root map is an isomorphism: it is the inverse roots comparison, the
image of the residue etale root isomorphism, and the coefficient-forgetting comparison isomorphism.
Apply the residue Kummer unit theorem to the full pro-etale Kummer sequence through this kernel
isomorphism. Extract the Tate-line derived unit from coefficient compatibility and compose the
units. The normalized pro root-map scalar identity identifies the resulting Ext class with the given
A-Kummer unit. -/
theorem pro_kummer_derived_unit
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) (hR : (n : ULift.{u + 1} (ZMod n)) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (φ : ULift.{u + 1} (ZMod n) →+* A)
    (cR : GeoCartierClass (ULift.{u + 1} (ZMod n)) n hR i)
    (cA : GeoCartierClass A n hA i)
    (hcompat : GeoCartierScalarCompatibility φ n hR hA i cR cA) :
    CartierScalarUnit (cartierForget A Z) (Scheme.proEtaleUnitsSheaf Z)
      (geoCartierLine A n hA Z) 1 (cartierProKummerUnit A n hA Z hn hZ) := by
  let R := ULift.{u + 1} (ZMod n)
  unfold GeoCartierScalarCompatibility at hcompat
  obtain ⟨η, θ, hη, hθ, hηunit, hθunit, hsquare⟩ := hcompat
  have : IsIso (Etale.ordinaryFiniteRootMap R n hR Z) :=
    Etale.residueFiniteRootMap_isIso Z n hR
  have : IsIso (cartierForgetComparison R Z (Scheme.finiteEtaleTateLine Z n R hR)) := by
    unfold cartierForgetComparison
    erw [← forgetComparisonIso_hom R Z]
    infer_instance
  have : IsIso (cartierProRootMap R n hR Z hn hZ) := by
    unfold cartierProRootMap
    infer_instance
  have hRu := CategoryTheory.Sheaf.ConstantResidue.kummer_iso_derived_unit
    (Scheme.ProEt.topology Z) n hn (Scheme.proEtaleRootsOfUnitySheaf Z n)
    (Scheme.proEtaleUnitsSheaf Z) (geoCartierLine R n hR Z)
    (Scheme.proEtaleRootsOfUnityInclusion Z n) (kernel.condition _)
    (cartierProKummer_exact Z n hn hZ)
    (asIso (cartierProRootMap R n hR Z hn hZ))
  unfold GeoCartierScalarUnit at hθunit
  have hθunit' : (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).DerivedUnit _ _ θ := by
    simpa only [Functor.DerivedUnit, Sheaf.IsDerivedBaseChange,
      Sheaf.derivedRestrictScalars, Category.assoc] using hθunit
  have hcomp := Functor.derivedExtUnit_comp
    (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ) (cartierForget R Z) 1
    ((cartierProKummer_exact Z n hn hZ).extClass.comp
      (Ext.mk₀ (cartierProRootMap R n hR Z hn hZ)) (add_zero 1)) θ hRu hθunit'
  have hγ := pro_root_scalar n hn φ hR hA Z hZ θ hθ
  have hiso := Functor.derivedExtUnit_iso
    ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ) ⋙ (cartierForget R Z))
    (cartierForget A Z) (Iso.refl _) _ _ 1 _ hcomp
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.comp_id] at hiso
  erw [hγ] at hiso
  unfold CartierScalarUnit cartierProKummerUnit cartierKummerClass
  exact hiso
end AlgebraicGeometry.ProEtale
