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

/-! # Naturality of the normalized scalar-extension section

## References

* Zheng Construction 4.1 and Stacks 03CZ, the scalar-extension unit on sheaves
* Zheng Construction 4.1 and Stacks 03CZ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r u
open CategoryTheory Opposite
namespace WeilConjectures.SemilinearSections

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] scalarExtensionSection
attribute [local implicit_reducible] transition

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
  (A : ScalarData.{c, v, max c v r} φ) (M : Mod.{c, v, max c v r} J R)

private theorem section_unit (U : Cᵒᵖ) (x : M.val.obj U) :
    scalarExtensionSection.{c, v, max c v r} φ A M U x =
      (A.ordinaryAdjunction.unit.app M).val.app U x := by
  unfold scalarExtensionSection
  rw [← A.unit_section]
  exact congrArg (fun f ↦ f.val.app U ((A.ordinaryAdjunction.unit.app M).val.app U x))
    (eqToIso (A.model.obj_eq M)).hom_inv_id

/-- The normalized scalar-extension section commutes with all restrictions in the site. -/
private theorem scalarExtensionSection_naturality {U V : Cᵒᵖ} (p : U ⟶ V)
    (x : M.val.obj U) :
    (A.model.E.obj M).val.map p (scalarExtensionSection.{c, v, max c v r} φ A M U x) =
      scalarExtensionSection.{c, v, max c v r} φ A M V (M.val.map p x) := by
  rw [section_unit.{c, v, r}, section_unit.{c, v, r}]
  exact (PresheafOfModules.naturality_apply
    (A.ordinaryAdjunction.unit.app M).val p x).symm

private theorem generic_transition_apply
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{u + 1} C]
    (B : ℕ → Sheaf J CommRingCat.{u + 1}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {m n : ℕ} (h : n ≤ m)
    (M : SemilinearSections.Systems.{u + 1, u, u + 1} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (m, U.unop))) :
    ((SemilinearSections.transition.{u + 1, u, u + 1} J B τ h).app M).val.app U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  exact congrFun (eq_of_heq
    ((SemilinearSections.transition_exists.{u + 1, u, u + 1}
      J B τ h).exists.choose_spec M U)) x

/-- The scalar-adjunction unit commutes with the evaluated horizontal transition.
The two explicit evaluated sections allow different scalar-restriction carriers.
-/
theorem scalarExtensionSection_transition
    {D : Type (u + 1)} [Category.{u} D] (K : GrothendieckTopology D)
    [EssentiallySmall.{u + 1} D]
    (B : ℕ → Sheaf K CommRingCat.{u + 1}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {R : Sheaf (coefficientSequenceTopology K) CommRingCat.{u + 1}}
    (φ : R ⟶ systemRing K B τ)
    (A : ScalarData.{u + 1, u, u + 1} φ)
    (M : Mod.{u + 1, u, u + 1} (coefficientSequenceTopology K) R)
    {m n : ℕ} (h : n ≤ m) (U : Dᵒᵖ) (x : M.val.obj (op (m, U.unop)))
    (v : ((evaluation.{u + 1, u, u + 1} K B τ m).obj (A.model.E.obj M)).val.obj U)
    (w : ((evaluation.{u + 1, u, u + 1} K B τ n).obj (A.model.E.obj M)).val.obj U)
    (hv : HEq v (scalarExtensionSection.{u + 1, u, u + 1}
      φ A M (op (m, U.unop)) x))
    (hw : HEq w (scalarExtensionSection.{u + 1, u, u + 1}
      φ A M (op (n, U.unop))
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x))) :
    HEq (((transition.{u + 1, u, u + 1} K B τ h).app
      (A.model.E.obj M)).val.app U v) w := by
  have hv' : v = scalarExtensionSection.{u + 1, u, u + 1}
      φ A M (op (m, U.unop)) x := eq_of_heq hv
  have hw' : w = scalarExtensionSection.{u + 1, u, u + 1}
      φ A M (op (n, U.unop))
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := eq_of_heq hw
  rw [hv', hw']
  exact heq_of_eq ((generic_transition_apply K B τ h (A.model.E.obj M) U _).trans
    (scalarExtensionSection_naturality.{u + 1, u, u + 1}
      (coefficientSequenceTopology K) φ A M
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x))

end WeilConjectures.SemilinearSections
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
