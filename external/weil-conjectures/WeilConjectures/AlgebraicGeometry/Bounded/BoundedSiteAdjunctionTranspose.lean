/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom

/-! # Chosen-compactification normalization of bounded site adjunction transposes

Source: Stacks Project, Tag 0B65, lemma-transformation-between-functors-and-adjoints;
blueprint thm-sf-ambient-adjoint-class, bounded Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose).

The comparison is the inverse of `compactSupportSiteComparison`, hence is built from
exact extension by zero and the named proper counit mate. The specified Hom map below
is defined by that comparison and the two existing adjunctions. Its inverse uniquely
defines the relative counit. No adjunction on all pro-etale objects is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The positive finite coefficient quotient is finite, including its standard size lift.
Source: blueprint def-pur-conventions; coefficient finiteness
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
instance boundedSiteCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

section Generic

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
variable (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
variable (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ H)

/-- The specified Hom-chain function, using the identity etale-origin witness and the
same compactification throughout. Source: Stacks Tag 0B65; blueprint bounded Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
def boundedSiteTranspose
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (z : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (D(ν^*(X)[ModuleCat.{u + 1} A]).obj J.obj) ⟶ L) :
    D(ν^*(X)[ModuleCat.{u + 1} A]).obj J.obj ⟶
      D(ν^*(X)[ModuleCat.{u + 1} A]).obj (H.obj ((R(ν_*(Y)[ModuleCat.{u + 1} A])).obj L)) :=
  D(ν^*(X)[ModuleCat.{u + 1} A]).map
    ((adj.homEquiv J.obj _)
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ L
        ((compactSupportSiteComparison A c).inv.app J ≫ z)))

/-- The comparison of right-adjoint objects is the image of the actual comparison unit.
Source: Stacks Tag 0B65; blueprint bounded site transpose, rho
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
def boundedSiteRho
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    D(ν^*(X)[ModuleCat.{u + 1} A]).obj (H.obj K) ⟶
      D(ν^*(X)[ModuleCat.{u + 1} A]).obj
        (H.obj (R(ν_*(Y)[ModuleCat.{u + 1} A]).obj
          (D(ν^*(Y)[ModuleCat.{u + 1} A]).obj K))) :=
  D(ν^*(X)[ModuleCat.{u + 1} A]).map
    (H.map ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app K))

end Generic

end AlgebraicGeometry.ProEtale
