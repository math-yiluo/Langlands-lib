/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Bounded-below pro-etale comparison

Source: blueprint main-20261015, sec-proetale-coefficients/sk-prop-sf-comparison,
statement and proof; Stacks Tags 099V, 099W and 03Q6 (blueprint:
theorem-bounded-below-cohomology-comparison).

The affine formula is stated on bounded-below injective representatives. The source
complex of its comparison map is the termwise filtered colimit, which represents the
filtered derived colimit because filtered colimits of modules are exact.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The canonical global-sections comparison, obtained by applying derived etale sections
to the derived adjunction unit and then the Leray isomorphism. No finiteness or commutativity
is required of the coefficient ring. Source: Stacks 099V and 099W
(blueprint: theorem-bounded-below-cohomology-comparison). -/
noncomputable def boundedBelowComparisonGlobalSections (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] :
    DerivedCategory.Plus.ι ⋙ Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.ι ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X :=
  let L := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus
  let R := comparisonLowerStar (ModuleCat.{u + 1} Λ) X
  let Γ := Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  (Functor.leftUnitor (DerivedCategory.Plus.ι ⋙ Γ)).inv ≫
    Functor.whiskerRight (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit
      (DerivedCategory.Plus.ι ⋙ Γ) ≫
    (Functor.associator L R.rightDerivedFunctorPlus (DerivedCategory.Plus.ι ⋙ Γ)).hom ≫
    Functor.whiskerLeft L
      ((Functor.associator R.rightDerivedFunctorPlus DerivedCategory.Plus.ι Γ).inv ≫
        Functor.whiskerRight R.rightDerivedFunctorPlusCompatibility.hom Γ ≫
        (Functor.associator DerivedCategory.Plus.ι R.rightDerivedFunctor Γ).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (comparisonLowerStarCompRightDerivedGlobalSectionsIso
            (ModuleCat.{u + 1} Λ) X).hom)

/-- The derived unit, full faithfulness on D+ and the canonical global-sections comparison.
Source: blueprint main-20261015, theorem-bounded-below-cohomology-comparison; Stacks 099V and 099W
(blueprint: theorem-bounded-below-cohomology-comparison).

Proof:
1. Apply the geometric comparison to addition and each scalar endomorphism. Naturality
makes the adjunction module-linear for any ring. The inverse image preserves kernels
and, as a left adjoint, cokernels. Both functors are additive and inverse image is exact.
The general coefficient unit theorem theorem-bounded-below-cohomology-comparison gives
invertibility of the underived unit. Exactness preserves D+ by
situation-conventions.
2. Good truncation gives a bounded-below representative of K. Choose a bounded-below
injective resolution I (theorem-bounded-below-cohomology-comparison). The functors of
theorem-bounded-below-cohomology-comparison compute right derived direct image and sections
on such resolutions; these module categories have enough injectives.
3. To construct the derived adjunction, resolve N by J. Direct image of J is K-injective
by theorem-bounded-below-cohomology-comparison. Use
theorem-bounded-below-cohomology-comparison and theorem-bounded-below-cohomology-comparison to
identify Hom(LM,N) with Hom(M,RRN). A resolution map j:LM -> J transposes to Rj after the unit.
4. Each LI^r is R-acyclic by theorem-bounded-below-cohomology-comparison (the general
Grothendieck-coefficient upstream interface also states this). Injective terms of J are
acyclic by lemma-weil-pbc-leray-acyclicity. Thus
lemma-acyclic-resolutions--1 makes Rj a quasi-isomorphism. The underived unit
on I is termwise invertible by theorem-bounded-below-cohomology-comparison. Consequently
the actual derived unit, represented by Rj after that unit, is invertible.
5. The derived adjunction sends Lf to eta_H after f. Since eta_H is invertible, the actual
map on Hom sets is bijective, proving full faithfulness.
6. R preserves injectives because its left adjoint is exact. On a pro-etale injective
resolution J, etale sections of RJ equal pro-etale sections of J: direct image is
restriction and the inclusion preserves the terminal object. The equality respects
differentials and maps, and descends using theorem-bounded-below-cohomology-comparison. Composing
this canonical Leray comparison with derived sections of the unit gives precisely
boundedBelowComparisonGlobalSections and proves its invertibility. -/
theorem boundedBelowComparison (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] :
    IsIso (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit ∧
      Nonempty (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.FullyFaithful ∧
      IsIso (boundedBelowComparisonGlobalSections X Λ) := by
  have hu := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} Λ) X
  have hunit : IsIso (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
        (fun _ _ ↦ inferInstance)
        (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective
          (ModuleCat.{u + 1} Λ) X I) K
  refine ⟨hunit, ⟨Adjunction.fullyFaithfulLOfIsIsoUnit
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus⟩, ?_⟩
  unfold boundedBelowComparisonGlobalSections
  infer_instance

end AlgebraicGeometry.ProEtale
