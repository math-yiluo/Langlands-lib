/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SiteHomComparisonThick
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeHomology
import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Site comparison for internal Hom from a flat lisse sheaf

The finite-coordinate maps are actual evaluation maps at the chosen basis vectors.
Finite products in these additive categories are the finite direct sums in the source.

## References

* Stacks Tags 00NZ, 08JI, 08JB, 03EO and 095I
* Stacks 03EO, naturality of evaluation
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
attribute [local instance 20000] isNoetherian_of_finite
attribute [local irreducible] Padic.coefficientExtensionAbsoluteValue
  Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionIdeal
universe u c d v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonoidalClosed

namespace AlgebraicGeometry.ProEtale

/-- Both-variable naturality, stated with abstract functors so that it does not
unfold the derived tensor structures while checking the equation. The specialization
below supplies exactly the existing evaluation comparison. -/
def lisseFlatHomNaturality
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{v} D]
    (H : Cᵒᵖ ⥤ C ⥤ C) (G : Dᵒᵖ ⥤ D ⥤ D) (F : C ⥤ D)
    (β : ∀ K M : C, F.obj ((H.obj (op K)).obj M) ⟶
      (G.obj (op (F.obj K))).obj (F.obj M)) (K N : C) : Prop :=
  ∀ (K' N' : C) (f : K' ⟶ K) (g : N ⟶ N'),
    F.map ((H.map f.op).app N ≫ (H.obj (op K')).map g) ≫ β K' N' =
      β K N ≫ (G.map (F.map f).op).app (F.obj N) ≫
        (G.obj (op (F.obj K'))).map (F.map g)

private theorem homComparison_naturality
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{v} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxMonoidal] (K N : C) :
    lisseFlatHomNaturality internalHom internalHom F
      (fun K N ↦ (Functor.LaxMonoidal.ihomComparison F K).app N) K N := by
  intro K' N' f g
  change F.map ((pre f).app N ≫ (ihom K').map g) ≫
    (Functor.LaxMonoidal.ihomComparison F K').app N' =
    (Functor.LaxMonoidal.ihomComparison F K).app N ≫
      (pre (F.map f)).app (F.obj N) ≫ (ihom (F.obj K')).map (F.map g)
  have h : F.map ((ihom K').map g) ≫
      (Functor.LaxMonoidal.ihomComparison F K').app N' =
      (Functor.LaxMonoidal.ihomComparison F K').app N ≫
        (ihom (F.obj K')).map (F.map g) :=
    (Functor.LaxMonoidal.ihomComparison F K').naturality g
  rw [F.map_comp, Category.assoc, h, ← Category.assoc,
    Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app, Category.assoc]

private theorem site_iso_of_pairing
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) [(comparisonUpperStar B X).PreservesFlat]
    (Q K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    [ExactPairing Q K] : IsIso (siteComparisonEvaluationHom B X K N) := by
  let : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal B X
  unfold siteComparisonEvaluationHom
  exact Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing _ Q K N

attribute [local irreducible] _root_.DerivedCategory.monoidalClosed

private theorem localized_pairing
    {C : Type c} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ n, HasRightDual (P.X n)] :
    Nonempty (ExactPairing (_root_.DerivedCategory.Q.obj P.rightDual)
      (_root_.DerivedCategory.Q.obj P)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory C
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_exactPairing_Q_obj_rightDual P a b
  exact ⟨BraidedCategory.exactPairing_swap _ _⟩

private theorem lisse_pairing (A : Type (u + 1)) [CommRing A] [Finite A] {X : Scheme.{u}}
    (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) [Scheme.IsFiniteLocallyConstantSheaf P]
    (hP : ObjectProperty.flat P) :
    ∃ D, Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X D ∧
      Nonempty (ExactPairing D ((_root_.DerivedCategory.singleFunctor _ 0).obj P)) := by
  let C := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj P
  have hCl (n : ℤ) : Scheme.IsFiniteLocallyConstantSheaf (C.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
        (HomologicalComplex.singleObjXSelf _ 0 P).symm
    · exact Scheme.IsFiniteLocallyConstantSheaf.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hCf (n : ℤ) : ObjectProperty.flat (C.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 P).symm hP
    · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  let _ (n : ℤ) : HasRightDual (C.X n) :=
    { rightDual := (ihom (C.X n)).obj (𝟙_ _)
      exact := letI := Etale.exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (C.X n) (hCf n)
        BraidedCategory.exactPairing_swap _ _ }
  obtain ⟨ep⟩ := localized_pairing C 0 0
  refine ⟨_, Etale.constructibleFiniteTor_Q_obj_of_flat A (CochainComplex.rightDual C) (-0) (-0)
    (fun n ↦ ?_) (fun n ↦ ?_), ⟨@exactPairingCongrRight _ _ _ _ _ _ ep
      ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app P)⟩⟩
  · -- the dual of a lisse flat sheaf is flat, being dualizable
    exact IsDualizable.flat ⟨@HasRightDual.mk _ _ _ _ (C.X (-n))
      (Etale.exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (C.X (-n)) (hCf (-n)))⟩
  · -- and lisse
    have := Etale.isFiniteLocallyConstantSheaf_ihom_unit_of_flat (C.X (-n)) (hCf (-n))
    exact Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf this

end AlgebraicGeometry.ProEtale
