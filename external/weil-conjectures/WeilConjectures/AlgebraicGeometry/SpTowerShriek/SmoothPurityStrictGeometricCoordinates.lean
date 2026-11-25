/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsBaseExistence
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsTransitionExistence
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteSectionInverseImages
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOrdinaryComp
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOrdinaryCompEvaluation

/-! # Constant-section geometric coordinates on strict ell-power systems

Source: Zheng Construction 4.1 and Lemma 4.10; blueprint operations proof (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
universe u c v r
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
open SemilinearSections
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem exact_derived_congr
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    {L L' : A ⥤ D} [L.Additive] [L'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L'] (h : L = L') :
    L.mapDerivedCategory = L'.mapDerivedCategory := by
  subst L'
  rfl

end AlgebraicGeometry.ProEtale.SpTowerShriek
