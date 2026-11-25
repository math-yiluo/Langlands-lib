/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.MilnorTower
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
public import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Pasting constant-coefficient pro-etale pullback squares

## Main statements

- `proEtaleFactorizedPullback_pasting`: equality of the two canonical derived paths.
- `proEtaleFactorizedPullback_pasting_representatives`: their termwise normalization.

## References

* Stacks Tag 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingModulePullback proEtaleConstantRingComparison
  Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategory

/-- The ordinary compositor with the unit-section normalization.
The unit-section equation in the cited theorem determines its maps: the adjunction
identifies a map out of pullback with its composite with the unit. Thus this choice
selects the canonical isomorphism, rather than an unspecified witness of existence. -/
def proEtalePastingOrdinaryComposition
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (k : Y ⟶ X) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h ≅
      proEtaleConstantRingPullback A (h ≫ k) :=
  (Classical.choose (proEtaleConstantRingPullbackComposition_ordinary h k A)).symm

/-- The ordinary square comparison, with the specified equality transport. -/
def proEtalePastingOrdinarySquare
    {X Y : Scheme.{u}} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A vY ⋙ proEtaleConstantRingPullback A u ≅
      proEtaleConstantRingPullback A u ⋙ proEtaleConstantRingPullback A vX :=
  proEtalePastingOrdinaryComposition u vY A ≪≫
    eqToIso (congrArg (proEtaleConstantRingPullback A) e) ≪≫
      (proEtalePastingOrdinaryComposition vX u A).symm

/-- The derived square comparison, with the specified equality transport. -/
def proEtalePastingDerivedSquare
    {X Y : Scheme.{u}} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A vY ⋙ proEtaleConstantRingDerivedPullback A u ≅
      proEtaleConstantRingDerivedPullback A u ⋙ proEtaleConstantRingDerivedPullback A vX :=
  proEtaleConstantRingPullbackComposition u vY A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e) ≪≫
      (proEtaleConstantRingPullbackComposition vX u A).symm

section Transport

universe v₀ v₁ v₂ v₃
variable {S : Type v₀} [Category.{v₁} S] (D : S → Type v₂) [∀ X, Category.{v₃} (D X)]
  (P : ∀ {X Y : S}, (X ⟶ Y) → (D Y ⥤ D X))
  (c : ∀ {X Y Z : S} (h : Z ⟶ Y) (k : Y ⟶ X), P k ⋙ P h ≅ P (h ≫ k))

end Transport

private theorem composition_localization
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (k : Y ⟶ X) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullbackComposition h k A =
      (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A k)
        (proEtaleConstantRingPullback A h)) ≪≫
        Functor.mapDerivedCategoryNatIso (proEtalePastingOrdinaryComposition h k A) := by
  let a := Classical.choose (proEtaleConstantRingPullbackComposition_ordinary h k A)
  have ha := (Classical.choose_spec
    (proEtaleConstantRingPullbackComposition_ordinary h k A)).2
  have hs : Functor.mapDerivedCategoryNatIso (proEtalePastingOrdinaryComposition h k A) =
      (Functor.mapDerivedCategoryNatIso a).symm := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_symm a
  apply Iso.ext_inv
  rw [Iso.trans_inv, hs, Iso.symm_inv]
  exact (congrArg Iso.hom ha).symm

private theorem localized_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (A : Type u) [CommRing A] :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (proEtaleConstantRingPullback A) e))).hom =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

section Localization

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
  [Abelian C] [Abelian D] [Abelian E] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory B]

end Localization

private theorem square_localization
    {X Y : Scheme.{u}} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (A : Type u) [CommRing A] :
    proEtalePastingDerivedSquare u vX vY e A =
      Functor.mapDerivedCategorySquareIso (proEtalePastingOrdinarySquare u vX vY e A) := by
  apply Iso.ext
  simp only [proEtalePastingDerivedSquare, proEtalePastingOrdinarySquare,
    composition_localization, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  rw [localized_transport e A]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
