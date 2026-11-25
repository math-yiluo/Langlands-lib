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
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic

/-! # The prescribed ordinary system as a strict system

The levels and transitions are literally the existing evaluation and transition operations.
Their strict laws follow from the section formula and the presheaf functor laws.

## References

* Zheng Construction 4.1
* Stacks 03D1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory Opposite

section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.SemilinearSections.OrdinarySource

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)

-- Keep the section map separate from the coefficient transports during elaboration.
/-- The horizontal map on section carriers, separated from its scalar transports. -/
def sourceSection (M : Systems.{c, v, max c v r} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) :
    M.val.obj (op (m, U.unop)) → M.val.obj (op (n, U.unop)) :=
  fun x ↦ (((transition J B τ h).app M).val.app U) x

private theorem sourceTransition_apply (M : Systems.{c, v, max c v r} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (x : M.val.obj (op (m, U.unop))) :
    sourceSection.{c, v, r} J B τ M h U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x :=
  congrFun (eq_of_heq ((transition_exists J B τ h).exists.choose_spec M U)) x

attribute [local irreducible] sourceSection

/-- The identity horizontal map acts as the identity on sections. -/
theorem sourceStrict_identity (M : Systems.{c, v, max c v r} J B τ)
    (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    @Eq (M.val.obj (op (n, U.unop)))
      (sourceSection.{c, v, r} J B τ M (Nat.le_refl n) U x) x := by
  have he : (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op =
      𝟙 (op (n, U.unop)) := rfl
  have hi : M.val.map (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op x = x := by
    rw [he, M.val.map_id]
    rfl
  exact (sourceTransition_apply.{c, v, r} J B τ M (Nat.le_refl n) U x).trans hi

/-- Horizontal maps compose as presheaf restrictions. -/
theorem sourceStrict_compose (M : Systems.{c, v, max c v r} J B τ)
    {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    @Eq (M.val.obj (op (l, U.unop)))
      (sourceSection.{c, v, r} J B τ M (h.trans k) U x)
      (sourceSection.{c, v, r} J B τ M h U
        (sourceSection.{c, v, r} J B τ M k U x)) := by
  have he : (Prod.mkHom (homOfLE (h.trans k)) (𝟙 U.unop)).op =
      (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op ≫
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op := by
    apply Quiver.Hom.unop_inj
    apply Prod.hom_ext
    · exact Subsingleton.elim _ _
    · simp
  exact (sourceTransition_apply.{c, v, r} J B τ M (h.trans k) U x).trans
    ((M.val.congr_map_apply he x).trans
      ((M.val.map_comp_apply (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x).trans
        ((congrArg (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
          (sourceTransition_apply.{c, v, r} J B τ M k U x).symm).trans
          (sourceTransition_apply.{c, v, r} J B τ M h U
            (show M.val.obj (op (m, U.unop)) from
              sourceSection.{c, v, r} J B τ M k U x)).symm)))

/-- The strict system with exactly the prescribed evaluations and transitions. -/
def sourceStrictObject (M : Systems.{c, v, max c v r} J B τ) :
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) where
  level n := (evaluation J B τ n).obj M
  transition h := (transition J B τ h).app M
  identity n U x := by
    have he := sourceStrict_identity.{c, v, r} J B τ M n U x
    unfold sourceSection at he
    exact he
  compose h k U x := by
    have he := sourceStrict_compose.{c, v, r} J B τ M h k U x
    unfold sourceSection at he
    exact he

/-- Extraction of strict systems using exactly the prescribed component functors. -/
def sourceStrictFunctor : Systems.{c, v, max c v r} J B τ ⥤
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) where
  obj := sourceStrictObject.{c, v, r} J B τ
  map f :=
    { app := fun n ↦ (evaluation J B τ n).map f
      comm := fun h ↦ (transition J B τ h).naturality f }
  map_id M := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (evaluation J B τ n).map_id M
  map_comp f g := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (evaluation J B τ n).map_comp f g

end WeilConjectures.SemilinearSections.OrdinarySource

end
