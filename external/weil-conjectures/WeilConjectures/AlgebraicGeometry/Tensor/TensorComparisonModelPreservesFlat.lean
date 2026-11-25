/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Flat modules preserved by a normalized tensor model

Source: Stacks 06YS and 07A4.
(blueprint: lem-coef-semilinear-tensor-model-preserves-flat)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory
  CoefficientClosedStructure.tensor

variable {C₀ C₁ : Type c} [Category.{v} C₀] [Category.{v} C₁]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem siteFlat_of_catFlat (M : Mod.{c, v, max c v r} J₀ R₀)
    (h : letI := SheafOfModules.isMonoidal_W_independentCoefficients R₀
      letI := SheafOfModules.monoidalCategory R₀
      ObjectProperty.flat M) : SheafOfModules.IsFlatOnSite (J := J₀) (R := R₀) M := by
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R₀ M).symm h.2

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A normalized tensor model preserves flat modules.
Source: Stacks 06YS and 07A4, flat complexes and derived tensor comparison.
(blueprint: lem-coef-semilinear-tensor-model-preserves-flat).

Proof: put a flat module in degree zero. Its terms are flat (all other terms
vanish), and the bounded-above flat criterion makes it K-flat. The model sends
this complex to a K-flat complex. Mapping a single complex is isomorphic to the
single complex of the image module. The converse K-flat single-complex criterion
therefore makes that image categorically flat. The natural isomorphism between
categorical sheaf tensor and site sheaf tensor gives the asserted site flatness. -/
theorem tensorComparisonModel_preserves_flat
    (F : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₁ R₁)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S₀ : Closed.{c, v, r} J₀ R₀) (S₁ : Closed.{c, v, r} J₁ R₁)
    (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
    (μ : S₀.tensor ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ S₁.tensor)
    (t : TensorComparisonModel.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μ)
    (M : Mod.{c, v, max c v r} J₀ R₀)
    (hM : SheafOfModules.IsFlatOnSite (J := J₀) (R := R₀) M) :
    SheafOfModules.IsFlatOnSite (J := J₁) (R := R₁) (F.obj M) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R₀
  let := SheafOfModules.monoidalCategory R₀
  -- A single flat module is K-flat, and K-flatness of its image detects flatness.
  let P := (CochainComplex.singleFunctor (Mod.{c, v, max c v r} J₀ R₀) 0).obj M
  have hf : flatTerms.{c, v, r} J₀ R₀ P := by
    intro i
    apply siteFlat_of_catFlat.{c, v, r} J₀ R₀
    by_cases hi : i = 0
    · subst i
      exact ObjectProperty.prop_of_iso ObjectProperty.flat
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm
        (SheafOfModules.flat_to_cat R₀ M hM)
    · exact ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R₀ P 0 hf
  have ht := t.kflat P hk hf
  let := SheafOfModules.isMonoidal_W_independentCoefficients R₁
  let := SheafOfModules.monoidalCategory R₁
  let := SheafOfModules.symmetricCategory R₁
  let := SheafOfModules.tensorPreadditive R₁
  have (N : Mod.{c, v, max c v r} J₁ R₁) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft N) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R₁ N
    exact preservesColimitsOfSize_shrink _
  have (N : Mod.{c, v, max c v r} J₁ R₁) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight N) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have hcat := CategoryTheory.RingedDerivedNative.kFlat.{c, v, r} J₁ R₁ _ ht
  have hcat' := (HomotopyCategory.kFlat_quotient_obj_iff _).1 hcat
  have hs := ObjectProperty.prop_of_iso
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M) hcat'
  exact siteFlat_of_catFlat.{c, v, r} J₁ R₁ _
    ((CochainComplex.kFlat_single_obj_iff_flat (F.obj M) 0).1 hs)

end WeilConjectures.SemilinearSections
