/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierSourceComparison
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.ScalarBoundaryComparison
import WeilConjectures.AlgebraicGeometry.Cartier.CartierNormalizedScalarUnits
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProIntegralResidueDerivedUnit
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProIntegralScalar
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProRootScalar
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierScalarUnitDerivedUnit
import WeilConjectures.AlgebraicGeometry.ScalarUnitExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
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
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import all WeilConjectures.CategoryTheory.FlatScalarUnit
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import all WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Mathlib.CategoryTheory.Adjunction.Unique
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import all WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.SixFunctors.Finite.Stalk
import all Mathlib.CategoryTheory.Sites.Adjunction
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.AlgebraicGeometry.Scheme
import all WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import all WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.SixFunctors.Finite.Exact
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso

/-! # Coefficient square for comparison images of ordinary boundaries -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify AlgebraicGeometry.cartierEtaleAbHasExt
  AlgebraicGeometry.ProEtale.geoCartierIntegralExt AlgebraicGeometry.Etale.hasExt_sheaf_moduleCat
  AlgebraicGeometry.ProEtale.geoCartierModuleExt
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] comparisonUpperStar cartierUnitsComparison
  cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit
  cartierProIntegralGenerator cartierProRootMap cartierReducedEtale cartierReducedPro
  CartierEtaleReductionSpec CartierProReductionSpec cartierResidueReducedPro

private theorem ext_iso_precomp {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {X Y Z : C} (e : X ≅ Y) (κ : Ext X Z 2) :
    (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp κ (zero_add 2)) (zero_add 2) = κ := by
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    e.hom_inv_id, Ext.mk₀_id_comp]

private theorem square_transport
    {C E : Type*} [Category* C] [Category* E] [Abelian C] [Abelian E]
    [HasExt C] [HasExt E] (U : E ⥤ C) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X P Y : C} {X' P' Y' : E} (a : X ≅ P) (b : X' ≅ P')
    (η : P ⟶ U.obj P') (θ : Y ⟶ U.obj Y')
    (k : Ext X Y 2) (k' : Ext X' Y' 2)
    (h : (Ext.mk₀ η).comp
      (((Ext.mk₀ b.inv).comp k' (zero_add 2)).mapExactFunctor U) (zero_add 2) =
      ((Ext.mk₀ a.inv).comp k (zero_add 2)).comp (Ext.mk₀ θ) (add_zero 2)) :
    (Ext.mk₀ (a.hom ≫ η ≫ U.map b.inv)).comp
      (k'.mapExactFunctor U) (zero_add 2) = k.comp (Ext.mk₀ θ) (add_zero 2) := by
  have hh := congrArg (fun c ↦ (Ext.mk₀ a.hom).comp c (zero_add 2)) h
  simpa only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Iso.hom_inv_id, Ext.mk₀_id_comp] using hh

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
private theorem boundary_reduction_spec (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (_hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2) :
    Etale.SupportedKummerBoundary A n hA i hI hZ c →
      CartierEtaleReductionSpec A n hA i hI hZ c := by
  obtain ⟨β, hβ, hβuniq⟩ := Etale.cartierPoleBoundary_existsUnique i hI
  have hpole : Etale.cartierPoleBoundary i hI = β :=
    hβuniq _ (Classical.choose_spec (Etale.cartierPoleBoundary_existsUnique i hI)).1
  intro hc
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
  have : IsIso (geoCartierSourceComparison A i) := geoCartierSourceComparison_isIso A i
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

private theorem integral_derived_unit
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (cartierForget A Z).DerivedUnit
      ((lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D))
      (cartierProIntegralGenerator A i) := by
  let B := ULift.{u + 1} (ZMod N)
  let : NeZero N := ⟨hN.ne'⟩
  have hB : (N : B) = 0 :=
    congrArg (ULift.up : ZMod N → B) (ZMod.natCast_self N)
  let φ := (Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom
  obtain ⟨η, θ, hη, hθ, hηunit, hθunit⟩ :=
    geoCartier_normalized_scalar_units B A N hN hB hA φ i hZ
  let U := Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ
  let V := cartierForget B Z
  let F := (lowerStar AddCommGrpCat.{u + 1} i).obj
    ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let G := (lowerStar (ModuleCat.{u + 1} B) i).obj (geoCartierConstant B D)
  let H := (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)
  let η' : G ⟶ U.obj H := (lowerStar (ModuleCat.{u + 1} B) i).map η
  have hRu := pro_integral_residue_derived_unit N hN i
  have hηunit' : U.DerivedUnit G H η' := by
    exact geoCartierScalarUnit_derivedUnit φ Z G H η' hηunit
  have hcomp := Functor.scalar_unit_comp U V F G H
    (cartierProIntegralGenerator B i) η' hRu hηunit'
  have hγ := pro_supported_generator_scalar φ i η hη
  have hiso := Functor.scalar_unit_iso (U ⋙ V) (cartierForget A Z)
    (Iso.refl _) F H (cartierProIntegralGenerator B i ≫ V.map η') hcomp
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id] at hiso
  rw [hγ] at hiso
  exact hiso

/-- Naturality of normalized ordinary boundary classes after comparison inverse
image, with the supported-source mates still displayed in the coefficient map.
This asserts only an Ext equality, not a scalar-unit universal property.
Source: blueprint sk-lem-geo-cartier.proof.md, finite coefficient extension and
opening comparison paragraphs (blueprint: lem-sfb-cartier-boundary-scalar-square).
Proof: Represent each ordinary class by its relative supported Kummer boundary.
The pole extension and its complementary splitting are independent of coefficients.
Successive derived extension from the integral supported constant, first to Z/N,
then to R and S, gives the same boundary under the tensor associativity map
(x tensor r) tensor s mapped to x tensor phi(r)s. The supported constant and roots
line are flat over the source coefficient sheaf, so their derived extensions have
the ordinary degree-zero source and target even for a nonflat coefficient map.
The normalized units send constants r to phi(r) and pure roots r tensor z to
phi(r) tensor z. Thus this scalar naturality is an equality for the specified
maps, rather than for arbitrary comparison isomorphisms. Relative-boundary
uniqueness identifies the two resulting Ext representatives with kR and kS.
Apply exact comparison inverse image to this ordinary square. The comparison
adjunction unit preserves the two generator formulas. Constant and root generators
locally generate the sheafified sources, so the supplied eta and theta agree with
these transported coefficient maps. The closed-source mate then identifies the
source coefficient map with the displayed composite through the inverse S mate.
Naturality of exact-functor Ext and Yoneda composition gives the stated equality.
For empty support or zero coefficients this is an equality of zero classes. -/
theorem geoCartier_boundary_scalar_square
    (R S : Type (u + 1)) [CommRing R] [CommRing S] [Finite R] [Finite S]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (hS : (N : S) = 0)
    (φ : R →+* S) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (N : Γ(Z, ⊤)))
    (kR : Ext ((Etale.lowerStar (ModuleCat.{u + 1} R) i).obj
      (Etale.ordinaryFiniteConstant R D)) (Scheme.finiteEtaleTateLine Z N R hR) 2)
    (kS : Ext ((Etale.lowerStar (ModuleCat.{u + 1} S) i).obj
      (Etale.ordinaryFiniteConstant S D)) (Scheme.finiteEtaleTateLine Z N S hS) 2)
    (hkR : Etale.SupportedKummerBoundary R N hR i hI hZ kR)
    (hkS : Etale.SupportedKummerBoundary S N hS i hI hZ kS)
    (η : geoCartierConstant R D ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant S D))
    (θ : geoCartierLine R N hR Z ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj (geoCartierLine S N hS Z))
    (hnorm :
    (∀ (W : D.ProEtᵒᵖ) (a : R),
      η.hom.app W ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))).app W a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of S S))).app W (φ a)) ∧
    (∀ (W : Z.Etaleᵒᵖ) (a : R) (z : (Z.rootsOfUnitySheaf N).obj.obj W),
      θ.hom.app ((Scheme.toProEt Z).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
          (Scheme.finiteEtaleTateLine Z N R hR)).hom.app W
            (Scheme.finiteEtaleTateOneGenerator R N Z hR W a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} S) Z).unit.app
        (Scheme.finiteEtaleTateLine Z N S hS)).hom.app W
          (Scheme.finiteEtaleTateOneGenerator S N Z hS W (φ a) z))) :
    (Ext.mk₀ (geoCartierSourceComparison R i ≫
      (lowerStar (ModuleCat.{u + 1} R) i).map η ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).map
        (asIso (geoCartierSourceComparison S i)).inv)).comp
      ((kS.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} S) Z)).mapExactFunctor
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ)) (zero_add 2) =
    (kR.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} R) Z)).comp
      (Ext.mk₀ θ) (add_zero 2) := by
  let eR := asIso (geoCartierSourceComparison R i)
  let eS := asIso (geoCartierSourceComparison S i)
  let dR : GeoCartierClass R N hR i :=
    (Ext.mk₀ eR.inv).comp
      (kR.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} R) Z)) (zero_add 2)
  let dS : GeoCartierClass S N hS i :=
    (Ext.mk₀ eS.inv).comp
      (kS.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} S) Z)) (zero_add 2)
  have hdR : (Ext.mk₀ (geoCartierSourceComparison R i)).comp dR (zero_add 2) =
      kR.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} R) Z) := by
    exact ext_iso_precomp (Z := geoCartierLine R N hR Z) eR
      (kR.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} R) Z))
  have hdS : (Ext.mk₀ (geoCartierSourceComparison S i)).comp dS (zero_add 2) =
      kS.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} S) Z) := by
    exact ext_iso_precomp (Z := geoCartierLine S N hS Z) eS
      (kS.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} S) Z))
  have hRspec := comparison_reduction_spec R N hN hR i hI hZ kR dR
    (boundary_reduction_spec R N hN hR i hI hZ kR hkR) hdR
  have hSspec := comparison_reduction_spec S N hN hS i hI hZ kS dS
    (boundary_reduction_spec S N hN hS i hI hZ kS hkS) hdS
  unfold CartierProReductionSpec cartierScalarBoundaryEquation at hRspec hSspec
  let U := cartierForget R Z
  let V := Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ
  have hu := scalar_unit_ext_bijective U
    (Q := V.obj (geoCartierLine S N hS Z)) (cartierProIntegralGenerator R i)
    (integral_derived_unit R N hN hR i hZ) 2
  have hη := pro_supported_generator_scalar φ i η hnorm.1
  have hθ := pro_root_scalar N hN φ hR hS Z hZ θ hnorm.2
  have hκ : (cartierProKummerUnit R N hR Z hN hZ).comp
      (Ext.mk₀ (U.map θ)) (add_zero 1) = cartierProKummerUnit S N hS Z hN hZ := by
    unfold cartierProKummerUnit cartierKummerClass
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hθ]
  have hforget : (dS.mapExactFunctor V).mapExactFunctor U =
      dS.mapExactFunctor (cartierForget S Z) := by
    have h := Ext.mapExactFunctor_comp_mk₀_eq_sheaf V U (cartierForget S Z)
      (Iso.refl _) dS
    simpa only [Iso.refl_hom, NatTrans.id_app, Ext.comp_mk₀_id,
      Ext.mk₀_id_comp] using h.symm
  have hsq : (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
      (dS.mapExactFunctor V) (zero_add 2) = dR.comp (Ext.mk₀ θ) (add_zero 2) := by
    apply hu.injective
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    rw [Ext.mk₀_comp_mk₀_assoc, hη, hforget, hSspec]
    rw [← Ext.comp_assoc_of_third_deg_zero, hRspec,
      Ext.comp_assoc_of_third_deg_zero, hκ]
  exact square_transport V eR eS ((lowerStar (ModuleCat.{u + 1} R) i).map η) θ
    (kR.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} R) Z))
    (kS.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} S) Z)) hsq

end AlgebraicGeometry.ProEtale
