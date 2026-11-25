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
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionEvaluationComparison
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement

/-! # Evaluation of ordinary scalar extension

## References

* Stacks Project, Modules on Sites, Section 03EK and Tag 03CY, applied to the vertical sequence
  topology
* Stacks Project, Section 03EK and Tag 03CY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory Opposite
namespace WeilConjectures.SemilinearSections

open scoped ChangeOfRings

attribute [local irreducible] scalarExtensionSection

private theorem evaluation_smul
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (D : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n, D (n + 1) ⟶ D n) (M : Systems.{c, v, max c v r} J D σ)
    (n : ℕ) (U : Cᵒᵖ) (a : (D n).obj.obj U)
    (x : M.val.obj (op (n, U.unop))) :
    a • (show ((evaluation.{c, v, max c v r} J D σ n).obj M).val.obj U from x) =
      (a • x : M.val.obj (op (n, U.unop))) := by
  change ((eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom.app U).hom a • x = _
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

/-- Evaluation of an ordinary coefficient extension represents coefficient-linear maps. -/
theorem scalarExtension_evaluation
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C)
    (B D : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, D (n + 1) ⟶ D n)
    (α : ∀ n, B n ⟶ D n)
    (φ : systemRing.{c, v, max c v r} J B τ ⟶ systemRing.{c, v, max c v r} J D σ)
    (hφ : ∀ (n : ℕ) (U : Cᵒᵖ), φ.hom.app (op (n, U.unop)) = (α n).hom.app U)
    (S : ScalarData.{c, v, max c v r} φ)
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) :
    ∃ Ψ : ∀ N : Mod.{c, v, max c v r} J (D n),
      ((evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M) ⟶ N) ≃
        ((evaluation.{c, v, max c v r} J B τ n).obj M ⟶ (res.{c, v, max c v r} (α n)).obj N),
      (∀ {N N'} (f : (evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M) ⟶ N)
        (g : N ⟶ N'), Ψ N' (f ≫ g) = Ψ N f ≫ (res.{c, v, max c v r} (α n)).map g) ∧
      (∀ N (f : (evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M) ⟶ N)
        (U : Cᵒᵖ) (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop)))
        (v : ((evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M)).val.obj U),
        HEq v (a • scalarExtensionSection.{c, v, r} φ S M (op (n, U.unop)) x) →
        f.val.app U v = a • (show N.val.obj U from (Ψ N f).val.app U x)) := by
  let Q := (evaluation.{c, v, max c v r} J B τ n).obj M
  obtain ⟨e, he⟩ := scalarExtension_evaluation_comparison.{c, v, r}
    J B D τ σ α φ hφ S M n
  let Ψ := fun N ↦ (Iso.homCongr e.symm (Iso.refl N)).trans
    (SheafOfModules.ScalarReductionProof.tensorHomEquiv (α n) Q N)
  refine ⟨Ψ, ?_, ?_⟩
  · intro N N' f g
    change SheafOfModules.ScalarReductionProof.tensorHomEquiv (α n) Q N'
        (e.hom ≫ (f ≫ g)) =
      SheafOfModules.ScalarReductionProof.tensorHomEquiv (α n) Q N (e.hom ≫ f) ≫
        (res.{c, v, max c v r} (α n)).map g
    exact (congrArg
      (SheafOfModules.ScalarReductionProof.tensorHomEquiv (α n) Q N')
      (Category.assoc e.hom f g).symm).trans
        (SheafOfModules.ScalarReductionProof.tensorHomEquiv_naturality_right
          (α n) Q (e.hom ≫ f) g)
  · intro N f U a x v hv
    let z := scalarExtensionSection.{c, v, r} φ S M (op (n, U.unop)) x
    have hv' : v = a •
        (show ((evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M)).val.obj U
          from z) :=
      (eq_of_heq hv).trans (evaluation_smul.{c, v, r} J D σ (S.model.E.obj M) n U a z).symm
    have hu : f.val.app U
        (show ((evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M)).val.obj U
          from z) = (Ψ N f).val.app U x := by
      exact (congrArg
        (fun t : ((evaluation.{c, v, max c v r} J D σ n).obj
          (S.model.E.obj M)).val.obj U ↦ f.val.app U t) (he U x)).symm
    rw [hv', map_smul]
    exact congrArg (fun t : N.val.obj U ↦ a • t) hu

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
