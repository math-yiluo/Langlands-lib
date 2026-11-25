/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictionInjectives
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Purity.PurityComparisonUnitInjectiveModel
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Site-comparison compatibility of the support boundary

Source: Stacks Project, `etale-cohomology.tex`, Tag 09XP, label
`section-cohomology-support`, with the etale/pro-etale refinement in the blueprint
(blueprint: lem-pur-support-comparison-boundary).

The statement records the two support long exact sequences and their canonical
adjunction-unit comparison ladder.  The boundary maps are normalized by the
snake boundary on every bounded-below injective model, so the sign convention is
part of the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The adjunction-unit comparison on sections over any etale object of `T`.
Source: blueprint comparison-global-cohomology and comparison-pullback clauses;
(blueprint: lem-pur-support-comparison-boundary).
Proof: evaluate the actual comparison adjunction unit at the chosen etale object;
naturality is the componentwise unit naturality equation. -/
noncomputable def finiteComparisonSectionUnit (T : Scheme.{u}) (A : Type (u + 1)) [Ring A]
    (V : Scheme.Etale T) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op V)) ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))) where
  app F := ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
    (op V)
  naturality F G f := by
    exact congrArg (fun t ↦ t.hom.app (op V))
      ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.naturality f)

/-- The canonical derived comparison on sections over an arbitrary etale object.
At the terminal object this is the same unit-normalized map as
`finiteComparisonGlobalSections`; at an open complement it is the comparison map
used in the boundary ladder.
Source: blueprint comparison-global-cohomology and comparison-pullback clauses;
(blueprint: lem-pur-support-comparison-boundary).
Proof: apply right-derived-plus base change to `finiteComparisonSectionUnit`; the
comparison pullback coherence identifies its pro-etale target with the restriction
of the comparison on the open complement. -/
noncomputable def finiteComparisonSection (T : Scheme.{u}) (A : Type (u + 1)) [Ring A]
    (V : Scheme.Etale T) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op V)).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op V))
      (G' := sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op ((Scheme.toProEt T).obj V)))
      (β := comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A)) (finiteComparisonSectionUnit T A V)

/-- The canonical degreewise comparison on sections over an etale object.
Source: blueprint comparison-map clauses
(blueprint: lem-pur-support-comparison-boundary).
Proof: whisker `finiteComparisonSection` by integer homology and reassociate the
composite functors.  For the terminal object this is the unit-normalized global
comparison of `finiteComparisonGlobalSections`; for an open object the pullback
coherence identifies the target with the restriction comparison. -/
noncomputable def finiteComparisonSectionHypercohomology
    (T : Scheme.{u}) (A : Type (u + 1)) [Ring A] (V : Scheme.Etale T) (q : ℤ) :
    Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) V q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) ((Scheme.toProEt T).obj V) q :=
  by
    simpa [Sheaf.sectionHypercohomologyFunctor] using
      (Functor.whiskerRight (finiteComparisonSection T A V)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
        (Functor.associator
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus
          ((sheafToPresheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) ⋙
            (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))).rightDerivedFunctorPlus)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q)).hom)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- A support boundary is the snake boundary on each injective section complex,
transported through the canonical right-derived comparison maps.
Source: Stacks Project Tag 09XP and (blueprint: lem-pur-support-comparison-boundary).
Proof: for an injective complex, the kernel-inclusion and restriction maps form a
short exact complex; its `ShortExact.δ` is the snake boundary. -/
def supportBoundaryNormalization {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A]
    {V W : C} (j : W ⟶ V)
    (δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    [∀ r : ℤ, Injective (I.obj.X r)],
    ∃ (w :
        (NatTrans.mapHomologicalComplex
          (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j)
          (ComplexShape.up ℤ)).app I.obj ≫
        (NatTrans.mapHomologicalComplex
          ((sheafSections J (ModuleCat.{u + 1} A)).map j.op)
          (ComplexShape.up ℤ)).app I.obj = 0)
      (hS : (ShortComplex.mk _ _ w).ShortExact),
      ∀ q : ℤ,
        Sheaf.supportSequenceModelBoundary J (ModuleCat.{u + 1} A) j ⊤ δ I
          ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ (Iso.refl _) q =
          hS.δ q (q + 1) rfl

end AlgebraicGeometry
