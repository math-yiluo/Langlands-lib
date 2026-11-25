/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.Scalar.ScalarExtUnitComposition
import WeilConjectures.CategoryTheory.Scalar.ScalarExtUnitIso
import WeilConjectures.CategoryTheory.Sites.ConstantResidue.ResidueKummerIsoDerivedUnit
import WeilConjectures.AlgebraicGeometry.Residue.ResidueFiniteRootMapIso
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement

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
-- Reuse the instance witnesses fixed by the ordinary derived-category interface.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] comparisonUpperStar cartierUnitsComparison
  cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit
  cartierProIntegralGenerator cartierProRootMap cartierReducedEtale cartierReducedPro
  CartierEtaleReductionSpec CartierProReductionSpec cartierResidueReducedPro

private theorem etale_root_scalar (n : ℕ) {R A : Type (u + 1)}
    [CommRing R] [CommRing A] (φ : R →+* A) (hR : (n : R) = 0) (hA : (n : A) = 0)
    (Z : Scheme.{u})
    (θ : Scheme.finiteEtaleTateLine Z n R hR ⟶
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine Z n A hA))
    (hθ : ∀ W a z, θ.hom.app W (Scheme.finiteEtaleTateOneGenerator R n Z hR W a z) =
      Scheme.finiteEtaleTateOneGenerator A n Z hA W (φ a) z) :
    Etale.ordinaryFiniteRootMap R n hR Z ≫
        (Etale.RawModuleScalarComparison.forget R Z).map θ =
      Etale.ordinaryFiniteRootMap A n hA Z := by
  ext W z
  change θ.hom.app W (Scheme.finiteEtaleTateOneGenerator R n Z hR W 1 z) =
    Scheme.finiteEtaleTateOneGenerator A n Z hA W 1 z
  have h := hθ W 1 z
  simpa only [map_one] using h

/-- Let n>0, A a finite commutative ring killed by n, Z a scheme on which n is invertible, and i:D→Z
an effective Cartier closed immersion. The normalized etale Kummer class G_m→forget(A_Z(1))[1] is a
degree-one unbounded scalar unit [def-sfb-cartier-reduction-data, def-sp-derived-scalar-ext-unit].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-cartier-etale-kummer-derived-unit).
Proof: For R=ULift(Z/n), the ordinary root map is an isomorphism. Apply the residue Kummer unit
theorem through this isomorphism to the etale Kummer sequence. The coefficient clause of the
existing ordinary supported Cartier Kummer theorem supplies the normalized derived unit
R_Z(1)→Res(A_Z(1)). Compose the two scalar units and identify composite coefficient forgetting with
direct forgetting. At a root z the composite root map sends z to 1 tensor z, by the pure tensor
normalization at a=1. Yoneda associativity then identifies its Ext representative with the published
Kummer unit. -/
theorem etale_kummer_derived_unit
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤))) :
    CartierScalarUnit (Etale.RawModuleScalarComparison.forget A Z) Z.gmSheaf
      (Scheme.finiteEtaleTateLine Z n A hA) 1 (cartierEtaleKummerUnit A n hA Z hZ) := by
  let R := ULift.{u + 1} (ZMod n)
  have hR : (n : R) = 0 :=
    congrArg (ULift.up : ZMod n → R) (ZMod.natCast_self n)
  let φ : R →+* A :=
    (Scheme.finiteEtaleTwistScalar n A hA).comp ULift.ringEquiv.toRingHom
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨κ, c, c₁, t, hc, hb, hu, hch, hc₁, hbase, hcoef⟩ :=
    Etale.ordinary_supported_kummer Z n hn A hA hZ i hI
  obtain ⟨κ₀, hb₀, hscalar⟩ := hcoef
  unfold Etale.SupportedKummerScalar at hscalar
  obtain ⟨η, θ, hη, hθ, hηunit, hθunit, hsquare⟩ := hscalar
  have : IsIso (Etale.ordinaryFiniteRootMap R n hR Z) :=
    Etale.residueFiniteRootMap_isIso Z n hR
  have hRu := CategoryTheory.Sheaf.ConstantResidue.kummer_iso_derived_unit
    Z.smallEtaleTopology n hn (Z.rootsOfUnitySheaf n) Z.gmSheaf
    (Scheme.finiteEtaleTateLine Z n R hR) (kernel.ι (n • 𝟙 Z.gmSheaf))
    (kernel.condition _) (Z.kummerSequence_shortExact n hZ)
    (asIso (Etale.ordinaryFiniteRootMap R n hR Z))
  unfold Etale.SupportedDerivedScalarUnit at hθunit
  have hθunit : (Sheaf.restrictScalars Z.smallEtaleTopology φ).DerivedUnit
      (Scheme.finiteEtaleTateLine Z n R hR) (Scheme.finiteEtaleTateLine Z n A hA) θ := by
    exact SheafExactDegreeZero.scalarUniversal_derivedUnit Z.smallEtaleTopology φ _ _ θ hθunit
  have hcomp := Functor.derivedExtUnit_comp
    (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    (Etale.RawModuleScalarComparison.forget R Z) 1
    ((Z.kummerSequence_shortExact n hZ).extClass.comp
      (Ext.mk₀ (Etale.ordinaryFiniteRootMap R n hR Z)) (add_zero 1)) θ hRu hθunit
  have hγ := etale_root_scalar n φ hR hA Z θ hθ
  have hiso := Functor.derivedExtUnit_iso
    ((Sheaf.restrictScalars Z.smallEtaleTopology φ) ⋙
      (Etale.RawModuleScalarComparison.forget R Z))
    (Etale.RawModuleScalarComparison.forget A Z) (Iso.refl _) _ _ 1 _ hcomp
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.comp_id] at hiso
  erw [hγ] at hiso
  unfold CartierScalarUnit cartierEtaleKummerUnit cartierKummerClass
  exact hiso
end AlgebraicGeometry.ProEtale
