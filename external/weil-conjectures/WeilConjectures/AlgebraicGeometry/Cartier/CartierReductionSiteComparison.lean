/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.ScalarBoundaryComparison
import WeilConjectures.AlgebraicGeometry.Cartier.CartierEtaleKummerDerivedUnit
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProKummerDerivedUnit
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProIntegralDerivedUnit
import WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Data.ZMod.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.CategoryTheory.DerivedUnit.DerivedScalarExtUnitZero
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass

/-! # Cartier reduction and site comparison
Source: blueprint main-20261015, Cartier comparison proof
(blueprint: lem-sp-cartier-reduction-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

private theorem kummer_comparison (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) (Z : Scheme.{u}) (hn : 0 < n)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    (Ext.mk₀.{u + 1} (cartierUnitsComparison Z)).comp
        (cartierProKummerUnit A n hA Z hn hZ) (zero_add 1) =
      ((cartierEtaleKummerUnit A n hA Z hZ).mapExactFunctor
        (comparisonUpperStar AddCommGrpCat.{u + 1} Z)).comp
        (Ext.mk₀.{u + 1} (cartierForgetComparison A Z
          (Scheme.finiteEtaleTateLine Z n A hA))) (add_zero 1) := by
  let F := comparisonUpperStar AddCommGrpCat.{u + 1} Z
  let a := cartierUnitsComparison Z
  let ψ : ((Z.kummerSequence n).map F) ⟶ cartierProKummerComplex Z n :=
    { τ₁ := cartierRootsComparison Z n
      τ₂ := a
      τ₃ := a
      comm₁₂ := by
        change cartierRootsComparison Z n ≫ kernel.ι (Scheme.proEtaleUnitsPower Z n) =
          F.map (kernel.ι (n • 𝟙 Z.gmSheaf)) ≫ a
        unfold cartierRootsComparison
        exact kernel.lift_ι _ _ _
      comm₂₃ := by
        change a ≫ Scheme.proEtaleUnitsPower Z n = F.map (n • 𝟙 Z.gmSheaf) ≫ a
        rw [F.map_nsmul, F.map_id]
        simp only [Scheme.proEtaleUnitsPower, Preadditive.nsmul_comp,
          Preadditive.comp_nsmul, Category.id_comp]
        exact Category.comp_id (n • a) }
  have hnat := ShortComplex.ShortExact.extClass_naturality
    ((Z.kummerSequence_shortExact n hZ).map_of_exact F)
    (cartierProKummer_exact Z n hn hZ) ψ
  have hroot : cartierRootsComparison Z n ≫ cartierProRootMap A n hA Z hn hZ =
      F.map (Etale.ordinaryFiniteRootMap A n hA Z) ≫
        cartierForgetComparison A Z (Scheme.finiteEtaleTateLine Z n A hA) := by
    unfold cartierProRootMap
    have he : (cartierRootsIso Z n hn hZ).hom = cartierRootsComparison Z n := by
      unfold cartierRootsIso
      rfl
    rw [← he, Iso.hom_inv_id_assoc]
  unfold cartierEtaleKummerUnit cartierProKummerUnit cartierKummerClass
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass]
  rw [← Ext.comp_assoc (Ext.mk₀ a) (cartierProKummer_exact Z n hn hZ).extClass
    (Ext.mk₀ (cartierProRootMap A n hA Z hn hZ)) (zero_add 1) (add_zero 1)
    (by omega)]
  rw [← hnat]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ψ, hroot]
  rfl
private theorem boundary_spec_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (_hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2) :
    Etale.SupportedKummerBoundary A n hA i hI hZ c ↔
      CartierEtaleReductionSpec A n hA i hI hZ c := by
  obtain ⟨β, hβ, hβuniq⟩ := Etale.cartierPoleBoundary_existsUnique i hI
  have hpole : Etale.cartierPoleBoundary i hI = β :=
    hβuniq _ (Classical.choose_spec (Etale.cartierPoleBoundary_existsUnique i hI)).1
  constructor
  · intro hc
    let := hI.isInvertible_dual_toModules
    let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
      (Scheme.Modules.dual i.ker.toModules)
    let W : Z.Opens :=
      ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    unfold Etale.SupportedKummerBoundary at hc
    obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, hext⟩ := hc W rfl
    have hEspec : Etale.CartierPoleBoundarySpec i hI hE.extClass := by
      intro W' hW'
      have hw : W' = W := by
        apply TopologicalSpace.Opens.ext
        exact hW'
      subst W'
      exact ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, rfl⟩
    have hEβ : hE.extClass = β := hβuniq _ hEspec
    unfold CartierEtaleReductionSpec cartierScalarBoundaryEquation
    rw [hpole, ← hEβ]
    unfold cartierEtaleKummerUnit cartierKummerClass
    simpa only [Ext.comp_assoc] using hext
  · intro hc
    let := hI.isInvertible_dual_toModules
    let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
      (Scheme.Modules.dual i.ker.toModules)
    unfold Etale.SupportedKummerBoundary
    intro W hW
    obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, he⟩ := hβ W hW
    refine ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, ?_⟩
    unfold CartierEtaleReductionSpec cartierScalarBoundaryEquation at hc
    rw [hpole, he] at hc
    unfold cartierEtaleKummerUnit cartierKummerClass at hc
    simpa only [Ext.comp_assoc] using hc

private theorem comparison_reduction_spec
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2)
    (d : GeoCartierClass A n hA i)
    (hc : CartierEtaleReductionSpec A n hA i hI hZ c)
    (hd : (Ext.mk₀.{u + 1} (geoCartierSourceComparison A i)).comp d (zero_add 2) =
      c.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)) :
    CartierProReductionSpec A n hA i hI hn hZ d := by
  have : IsIso (geoCartierSourceComparison A i) := cartierSourceComparison_isIso A i
  unfold CartierEtaleReductionSpec cartierScalarBoundaryEquation at hc
  have hκ := kummer_comparison A n hA Z hn hZ
  have h := Ext.scalar_boundary_comparison
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z)
    (Etale.RawModuleScalarComparison.forget A Z) (cartierForget A Z)
    (forgetComparisonIso A Z) (Etale.supportedIntegralGenerator A i)
    (cartierIntegralSourceIso i) (asIso (geoCartierSourceComparison A i))
    (cartierUnitsComparison Z) (Etale.cartierPoleBoundary i hI)
    (cartierEtaleKummerUnit A n hA Z hZ) (cartierProKummerUnit A n hA Z hn hZ)
    c d hc hd (by
      simpa only [forgetComparisonIso_hom, cartierForgetComparison, cartierForget,
        geoCartierLine, Functor.comp_obj] using hκ)
  unfold CartierProReductionSpec cartierScalarBoundaryEquation
    cartierProIntegralGenerator cartierProBoundary cartierBoundaryImage cartierForgetComparison
  simpa only [forgetComparisonIso_hom, asIso_hom, cartierForget, Functor.comp_obj,
    GeoCartierClass, geoCartierLine] using h

private theorem reducedEtale_boundary
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤))) :
    Etale.SupportedKummerBoundary A n hA i hI hZ
      (cartierReducedEtale A n hn hA i hI hZ) := by
  apply (boundary_spec_iff A n hn hA i hI hZ _).2
  unfold cartierReducedEtale
  exact (Classical.choose_spec (cartierReduction_existsUnique A n hn hA i hI hZ).1).1

private theorem reducedPro_eq_of_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (d : GeoCartierClass A n hA i)
    (hd : ∃ c : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
        (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2,
      Etale.SupportedKummerBoundary A n hA i hI hZ c ∧
      (Ext.mk₀.{u + 1} (geoCartierSourceComparison A i)).comp d (zero_add 2) =
        c.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)) :
    d = cartierReducedPro A n hn hA i hI hZ := by
  obtain ⟨c, hc, hd⟩ := hd
  have hs := comparison_reduction_spec A n hn hA i hI hZ c d
    ((boundary_spec_iff A n hn hA i hI hZ c).1 hc) hd
  unfold cartierReducedPro
  exact (Classical.choose_spec (cartierReduction_existsUnique A n hn hA i hI hZ).2).2 d hs

private theorem reducedEtale_eq_of_boundary
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2)
    (hc : Etale.SupportedKummerBoundary A n hA i hI hZ c) :
    c = cartierReducedEtale A n hn hA i hI hZ := by
  unfold cartierReducedEtale
  exact (Classical.choose_spec (cartierReduction_existsUnique A n hn hA i hI hZ).1).2 c
    ((boundary_spec_iff A n hn hA i hI hZ c).1 hc)

private theorem class_clauses (ℓ : ℕ) (hℓ : ℓ.Prime) (r : ℕ) (hr : 0 < r)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ℓ ^ r : ℕ) : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) :
    (Ext.mk₀.{u + 1} (geoCartierSourceComparison A i)).comp
        (cartierReducedPro A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) (zero_add 2) =
      (cartierReducedEtale A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ).mapExactFunctor
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z) ∧
    GeoCartierScalarCompatibility (cartierResidueAlgebra ℓ r A hA) (ℓ ^ r)
      (cartierResidue_cast ℓ r) hA i (cartierResidueReducedPro ℓ hℓ r i hI hZ)
      (cartierReducedPro A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) ∧
    GeoCartierChernEquation A (ℓ ^ r) hA i hI hZ
      (cartierReducedPro A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) := by
  obtain ⟨c, hc, hcoef, hbase, hexp⟩ := exists_geoCartierCycleClass ℓ hℓ
  obtain ⟨hiso, hchern, κ, hκ, hcomp⟩ := hc r hr A hA i hI hZ
  have hn := pow_pos hℓ.pos r
  have hκeq := reducedEtale_eq_of_boundary A (ℓ ^ r) hn hA i hI hZ κ hκ
  have heq := reducedPro_eq_of_comparison A (ℓ ^ r) hn hA i hI hZ
    (c r hr A hA i hI hZ) ⟨κ, hκ, hcomp⟩
  rw [heq, hκeq] at hcomp
  rw [heq] at hchern
  let : Finite (cartierResidueRing.{u} ℓ r) := cartierResidue_finite ℓ hℓ r
  have hR := hc r hr (cartierResidueRing.{u} ℓ r) (cartierResidue_cast ℓ r) i hI hZ
  have hReq := reducedPro_eq_of_comparison (cartierResidueRing.{u} ℓ r) (ℓ ^ r)
    hn (cartierResidue_cast ℓ r) i hI hZ
    (c r hr (cartierResidueRing.{u} ℓ r) (cartierResidue_cast ℓ r) i hI hZ) hR.2.2
  have hscalar := hcoef r hr (cartierResidueRing.{u} ℓ r) A
    (cartierResidue_cast ℓ r) hA (cartierResidueAlgebra ℓ r A hA) i hI hZ
  rw [heq, hReq] at hscalar
  refine ⟨hcomp, ?_, hchern⟩
  simpa only [cartierResidueReducedPro] using hscalar

/-- The full normalized Cartier pole-reduction comparison, including its scalar units,
coefficient extension, relative boundary, and characterization as the class c_D.

Source: blueprint main-20261015, sk-lem-geo-cartier.proof.md, (G1), derived reduction
and opening comparison paragraphs (blueprint: lem-sp-cartier-reduction-site-comparison).

Proof:
1. Finite geometric stalks of the supported integral constant are Z on D and zero
   elsewhere. Exact conservative stalks make multiplication by ℓ^r monic and identify
   its quotient, preserving one, with the supported residue constant.
2. The qcqs direct-image comparison on discrete coefficients, etale finite exactness,
   and the pro-etale degree-zero injective-resolution calculation give the canonical
   supported mates. Their unit equations preserve restriction to D and reduction.
3. Kummer on Z and on every pro-etale object U makes the power maps epic. Comparison
   preserves the kernel on comparison units. The section formula and etale roots
   pullback identify its map to full pro-etale roots with cartierRootsComparison.
4. Exact inverse image preserves the cone, its positive projection p, and the quotient
   quasi-isomorphism v. Thus it preserves the boundary -p v inverse. Push the pulled
   extension out along cartierUnitsComparison; its boundary is cartierProBoundary.
5. Apply divisible-extension derived reduction to the etale extension, its comparison
   pullback, and that pushout. Naturality gives equality of the complete R-linear
   arrows, under the quotient and Kummer-normalized identifications.
6. For the Kummer sequence, the homotopy with degree-zero component identity gives
   u v + k p = 0 in the derived category. Hence k inverse u = -p v inverse: the
   scalar unit is the positive Kummer connecting map. Shift comparisons give [2].
7. Extend scalars R to A. Supported constants and the etale rank-one roots line are
   flat, so source and target have the stated degree-zero identifications even when
   A is not R-flat. K-flat tensor comparison commutes extension with exact comparison
   inverse image. The scalar units uniquely characterize these identifications.
8. The local inverse equations are the frames of the dual ideal O(D), and the
   complementary canonical frame is zero in the relative extension. The torsor-H1
   boundary is therefore its positive line-bundle class. This proves both the
   supported relative boundary and the Chern equation; the integral generator is the
   scalar unit on the full supported sheaf. Its Hom universal property makes the
   normalized reduction unique as a module-derived arrow, not only after forgetting
   coefficients or after precomposing by the global constant-to-support map.
9. The class of lemma-cycle-class-cartier-divisor has this relative normalization and comparison
   mate. Uniqueness identifies it with cartierReducedPro, giving the last clause. -/
theorem cartier_reduction_site_comparison (ℓ : ℕ) (hℓ : ℓ.Prime) (r : ℕ) (hr : 0 < r)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ℓ ^ r : ℕ) : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) :
    IsIso (geoCartierSourceComparison A i) ∧
    IsIso (cartierRootsComparison Z (ℓ ^ r)) ∧
    CartierScalarUnit (Etale.RawModuleScalarComparison.forget A Z)
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj (Etale.supportedIntegralConstant D))
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) 0
      (Ext.mk₀.{u + 1} (Etale.supportedIntegralGenerator A i)) ∧
    CartierScalarUnit (cartierForget A Z)
      ((lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) 0
      (Ext.mk₀.{u + 1} (cartierProIntegralGenerator A i)) ∧
    CartierScalarUnit (Etale.RawModuleScalarComparison.forget A Z) Z.gmSheaf
      (Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hA) 1
      (cartierEtaleKummerUnit A (ℓ ^ r) hA Z hZ) ∧
    CartierScalarUnit (cartierForget A Z) (Scheme.proEtaleUnitsSheaf Z)
      (geoCartierLine A (ℓ ^ r) hA Z) 1
      (cartierProKummerUnit A (ℓ ^ r) hA Z (pow_pos hℓ.pos r) hZ) ∧
    (Ext.mk₀.{u + 1} (geoCartierSourceComparison A i)).comp
        (cartierReducedPro A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) (zero_add 2) =
      Ext.mapExactFunctor.{u + 1, u + 1}
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
        (cartierReducedEtale A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) ∧
    GeoCartierScalarCompatibility (cartierResidueAlgebra ℓ r A hA) (ℓ ^ r)
      (cartierResidue_cast ℓ r) hA i
      (cartierResidueReducedPro ℓ hℓ r i hI hZ)
      (cartierReducedPro A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) ∧
    Etale.SupportedKummerBoundary A (ℓ ^ r) hA i hI hZ
      (cartierReducedEtale A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) ∧
    GeoCartierChernEquation A (ℓ ^ r) hA i hI hZ
      (cartierReducedPro A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) ∧
    (∀ c : GeoCartierClass A (ℓ ^ r) hA i,
      (∃ κ : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
          (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hA) 2,
        Etale.SupportedKummerBoundary A (ℓ ^ r) hA i hI hZ κ ∧
        (Ext.mk₀.{u + 1} (geoCartierSourceComparison A i)).comp c (zero_add 2) =
          Ext.mapExactFunctor.{u + 1, u + 1}
            (comparisonUpperStar (ModuleCat.{u + 1} A) Z) κ) →
      c = cartierReducedPro A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ) := by
  have hn := pow_pos hℓ.pos r
  obtain ⟨hcomp, hcoef, hchern⟩ := class_clauses ℓ hℓ r hr A hA i hI hZ
  refine ⟨cartierSourceComparison_isIso A i,
    cartierRootsComparison_isIso Z (ℓ ^ r) hn hZ, ?_, ?_, ?_, ?_, hcomp, hcoef,
    reducedEtale_boundary A (ℓ ^ r) hn hA i hI hZ, hchern,
    reducedPro_eq_of_comparison A (ℓ ^ r) hn hA i hI hZ⟩
  · exact (Etale.supported_integral_derived_unit Z (ℓ ^ r) hn A hA i).extUnit_zero
  · exact pro_integral_derived_unit A (ℓ ^ r) hn hA (cartierResidue_cast ℓ r) i
      (cartierResidueAlgebra ℓ r A hA) _ _ hcoef
  · exact etale_kummer_derived_unit A (ℓ ^ r) hn hA i hI hZ
  · exact pro_kummer_derived_unit A (ℓ ^ r) hn hA (cartierResidue_cast ℓ r) i hZ
      (cartierResidueAlgebra ℓ r A hA) _ _ hcoef

end AlgebraicGeometry.ProEtale
