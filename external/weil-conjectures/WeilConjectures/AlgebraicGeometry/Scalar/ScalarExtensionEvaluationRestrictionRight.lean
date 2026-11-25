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
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement

/-! # Tensor comparison for evaluated scalar extension

## References

* Stacks Project, Modules on Sites, Section 03EK and Tag 03CY, applied to the vertical sequence
  topology
* Stacks Project, Section 03EK, restriction of pure tensors
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory Opposite
namespace WeilConjectures.SemilinearSections

open scoped ChangeOfRings

section Construction
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C)
  (B D : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, D (n + 1) ⟶ D n)
  (α : ∀ n, B n ⟶ D n)
  (φ : systemRing.{c, v, max c v r} J B τ ⟶ systemRing.{c, v, max c v r} J D σ)
  (M : Systems.{c, v, max c v r} J B τ) (n : ℕ)
  (e : ∀ U : Cᵒᵖ,
    (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
      (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M)).obj U ≅
      ((PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M)).obj U)
  (he : ∀ (U : Cᵒᵖ) (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop))),
    (e U).hom (a ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x) =
      (show (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop)) from a)
        ⊗ₜ[(B n).obj.obj U,(φ.hom.app (op (n, U.unop))).hom] x)

include he

private theorem evaluatedTensorRestriction_right
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M).map
      ((Prod.sectR n C).map f.unop).op
        ((e U).hom
          ((1 : (D n).obj.obj U) ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x)) =
    (1 : (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, V.unop)))
      ⊗ₜ[(systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, V.unop)),
        (φ.hom.app (op (n, V.unop))).hom]
        (show M.val.obj (op (n, V.unop)) from
          M.val.map ((Prod.sectR n C).map f.unop).op x) := by
  let i := ((Prod.sectR n C).map f.unop).op
  let P := SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M
  have hg := SheafOfModules.ScalarReductionProof.tensorRestriction_tmul φ M i
    (1 : (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop))) x
  simp only [map_one] at hg
  exact (congrArg (fun z ↦ P.map i z)
    (he U 1 x)).trans hg

/-- The right composite in tensor evaluation naturality has its generator value. -/
theorem scalarExtension_evaluation_restriction_right
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M).map
      ((Prod.sectR n C).map f.unop).op
        ((e U).hom
          ((1 : (D n).obj.obj U) ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x)) =
    (1 : (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, V.unop)))
      ⊗ₜ[(systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, V.unop)),
        (φ.hom.app (op (n, V.unop))).hom]
        (show M.val.obj (op (n, V.unop)) from
          M.val.map ((Prod.sectR n C).map f.unop).op x) := by
  exact evaluatedTensorRestriction_right.{c, v, r} J B D τ σ α φ M n e he f x

end Construction

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
