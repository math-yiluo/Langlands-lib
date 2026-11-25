/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleAffineEvaluation
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Restriction transport at a geometric point

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151; the explicit
pro-etale restriction and completed-coefficient argument is agent-written
(blueprint: lem-weil-point-automorphism-restriction-natural).

The inverse image is expressed in the canonical sectionwise coordinates of
`isoSectionwiseInverseImage`. Its distinguished coprojection is the identity in
these coordinates. `none` denotes integral coefficients and `some n` denotes
finite coefficients at positive exponent `n + 1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The two allowed scalar rings, lifted only to accommodate the site universe.
Source: Deligne (1.1.3); the coefficient convention of the node
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
def pointRestrictionScalars (a : Option ℕ) : RingCat.{max u (t + 1)} :=
  match a with
  | none => RingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
  | some n => RingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))

end AlgebraicGeometry.ProEtale
