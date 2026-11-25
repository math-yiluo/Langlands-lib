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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Evaluation preserves flat semilinear systems

Source: Zheng, Construction 4.1, and Stacks Project, Tag 08FC.
(blueprint: lem-pur-system-evaluation-flat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
private theorem evaluation_ring_app (n : ℕ) (U : Cᵒᵖ) :
    (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U =
      𝟙 ((ring.{c, v, max c v r} J (B n)).obj.obj U) := by
  change ((sheafToPresheaf J RingCat.{max c v r}).map
    (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm)).app U = _
  rw [eqToHom_map, eqToHom_app]
  rfl

private theorem evaluation_smul (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : Cᵒᵖ) (a : (B n).obj.obj U) (x : M.val.obj (op (n, U.unop))) :
    (a • (show ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U from x)) =
      ((show (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop)) from a) • x
        : M.val.obj (op (n, U.unop))) := by
  change (show (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop)) from
    ((eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U).hom a) • x = _
  erw [evaluation_ring_app.{c, v, r} J B τ n U]
  rfl

private theorem evaluation_ring_map (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop))) :
    (systemRing.{c, v, max c v r} J B τ).obj.map ((Prod.sectR n C).map f.unop).op a =
      (B n).obj.map f (show (B n).obj.obj U from a) := by
  have hn := (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.naturality f
  erw [evaluation_ring_app.{c, v, r} J B τ n U,
    evaluation_ring_app.{c, v, r} J B τ n V] at hn
  erw [Category.comp_id, Category.id_comp] at hn
  exact RingHom.congr_fun (congrArg RingCat.Hom.hom hn.symm) a

private def evaluationCoefficientEquiv (n : ℕ) (U : Cᵒᵖ) :
    (B n).obj.obj U ≃+*
      (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop)) := RingEquiv.refl _

private def evaluationSectionEquiv (n : ℕ)
    (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ) :
    ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U ≃+
      M.val.obj (op (n, U.unop)) := AddEquiv.refl _

private theorem evaluationSectionEquiv_smul (n : ℕ)
    (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (a : (B n).obj.obj U)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    evaluationSectionEquiv.{c, v, r} J B τ n M U (a • x) =
      evaluationCoefficientEquiv.{c, v, r} J B τ n U a •
        evaluationSectionEquiv.{c, v, r} J B τ n M U x :=
  evaluation_smul.{c, v, r} J B τ n M U a x

private theorem evaluationSectionEquiv_map (n : ℕ)
    (M : Systems.{c, v, max c v r} J B τ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    evaluationSectionEquiv.{c, v, r} J B τ n M V
      (((evaluation.{c, v, max c v r} J B τ n).obj M).val.map f x) =
      M.val.map ((Prod.sectR n C).map f.unop).op
        (evaluationSectionEquiv.{c, v, r} J B τ n M U x) := rfl

private theorem evaluationCoefficientEquiv_map (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (B n).obj.obj U) :
    evaluationCoefficientEquiv.{c, v, r} J B τ n V ((B n).obj.map f a) =
      (systemRing.{c, v, max c v r} J B τ).obj.map ((Prod.sectR n C).map f.unop).op
        (evaluationCoefficientEquiv.{c, v, r} J B τ n U a) :=
  (evaluation_ring_map.{c, v, r} J B τ n f a).symm

attribute [local irreducible] evaluation evaluationCoefficientEquiv evaluationSectionEquiv

/-- Evaluation preserves flatness on the coefficient sequence site.
Source: Zheng, Construction 4.1, and Stacks Project, Tag 08FC
(blueprint: lem-pur-system-evaluation-flat).
Proof: test the local finite-relation criterion at an object U of the original site.
Identify evaluated sections and scalars with those of the system at (n,U).
Apply flatness on the sequence site to this finite relation. Its covering sieve pulls
back along the vertical inclusion to a covering sieve of U, by the definition of the
sequence topology. Restrict its finite factorization witnesses to vertical arrows.
The coefficient and additive section identifications preserve restriction, scalar
multiplication, finite sums and products, so these are the required witnesses on U.
The argument also applies to empty finite families and empty covering sieves. -/
theorem evaluation_preserves_flat (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (hM : SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := coefficientSequenceTopology J) (R := systemRing J B τ) M) :
    SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := B n) ((evaluation.{c, v, max c v r} J B τ n).obj M) := by
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion.{c, v, max c v r, max c v r}
    (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
  intro U t a s hs
  have hs' := congrArg (evaluationSectionEquiv.{c, v, r} J B τ n M (op U)) hs
  simp only [map_sum, map_zero, evaluationSectionEquiv_smul.{c, v, r} J B τ n M (op U)] at hs'
  obtain ⟨S, hS, h⟩ :=
    SheafOfModules.local_equationalCriterion_of_isFlatOnSite.{c, v, max c v r, max c v r}
      (systemRing.{c, v, max c v r} J B τ) M hM (n, U) t
      (fun p ↦ evaluationCoefficientEquiv.{c, v, r} J B τ n (op U) (a p))
      (fun p ↦ evaluationSectionEquiv.{c, v, r} J B τ n M (op U) (s p)) hs'
  refine ⟨S.functorPullback (Prod.sectR n C), hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, z, hz, hb⟩ := h (n, V) ((Prod.sectR n C).map f) hf
  refine ⟨l, (fun p q ↦ (evaluationCoefficientEquiv.{c, v, r} J B τ n (op V)).symm (b p q)),
    (fun q ↦ (evaluationSectionEquiv.{c, v, r} J B τ n M (op V)).symm (z q)), ?_, ?_⟩
  · intro p
    apply (evaluationSectionEquiv.{c, v, r} J B τ n M (op V)).injective
    simp only [map_sum, evaluationSectionEquiv_smul.{c, v, r} J B τ n M (op V),
      AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      evaluationSectionEquiv_map.{c, v, r} J B τ n M f.op]
    exact hz p
  · intro q
    apply (evaluationCoefficientEquiv.{c, v, r} J B τ n (op V)).injective
    simp only [map_sum, map_mul, map_zero, RingEquiv.apply_symm_apply,
      evaluationCoefficientEquiv_map.{c, v, r} J B τ n f.op]
    exact hb q
end WeilConjectures.SemilinearSections
