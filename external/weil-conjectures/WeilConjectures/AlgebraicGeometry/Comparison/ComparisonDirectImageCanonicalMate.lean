/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-!
# Canonical derived direct-image comparison as a mate

Source: blueprint, `lem-weil-pbc-comparison-direct-image-canonical-mate`,
from `theorem-comparison-direct-images--1`; Stacks Tags 099R and 0B65.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The named bounded-below derived direct-image comparison is the mate of the
canonical pullback comparison.  This is the objectwise map used in the
proper-base-change comparison theorem.

Source: blueprint `lem-weil-pbc-comparison-direct-image-canonical-mate`,
proof of `theorem-comparison-direct-images--1`; Stacks Tag 0B65.

Proof (the node's steps): For each bounded-below etale complex, use the
pullback comparison and the etale counit to form the underived base-change
map, then take its mate under the pro-etale adjunction
(`proposition-comparison-etale-derived-category--5`, `def-weil-pbc-adjunction-mate`).
The mate bijection is natural in the complex, so these components form the
displayed natural transformation. On an affine target, evaluate on an
affine ind-etale basis and use derived-cohomology continuity twice; the
middle identification is evaluation of etale direct image on an injective
resolution (`theorem-bounded-below-cohomology-comparison--3`,
`corollary-cohomology-pro-etale-affine`,
`lemma-acyclicity-pulled-back-injectives`). Compare the final etale
sections with pro-etale sections using the global comparison and the
pro-etale restriction and exactness statements
(`theorem-bounded-below-cohomology-comparison--3`,
`lemma-acyclicity-pulled-back-injectives`,
`prop-weil-pbc-proetale-constant-exact`). On injective representatives,
the comparison-sections formula identifies the evaluated map with the
continuity map; direct-image injectivity and comparison acyclicity justify
the derived evaluations. Basis-derived detection then proves the mate is
an isomorphism (`proposition-comparison-morphism-inverse-image--3`,
`lemma-acyclicity-pulled-back-injectives`,
`theorem-comparison-direct-images`). Finally, the derived
base-change universal-property equation gives the displayed unit
factorization and hence the counit-mate normalization.
(blueprint: lem-weil-pbc-comparison-direct-image-canonical-mate).
-/
noncomputable def comparisonDirectImageCanonicalMate (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (u : U ⟶ V) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) u ⋙
        D+((comparisonUpperStar (ModuleCat.{u + 1} Λ) V)) ⟶
      D+((comparisonUpperStar (ModuleCat.{u + 1} Λ) U)) ⋙
        R+((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) u)) :=
  Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange u (ModuleCat.{u + 1} Λ))

/-- The canonical comparison is an isomorphism for quasi-compact,
quasi-separated morphisms.  Its component is the named mate, hence this
asserts invertibility of that particular morphism.

Source: blueprint `lem-weil-pbc-comparison-direct-image-canonical-mate`,
proof of `theorem-comparison-direct-images--1`; Stacks Tag 099R.
-/
theorem isIso_comparisonDirectImageCanonicalMate (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (u : U ⟶ V)
    [QuasiCompact u] [QuasiSeparated u] :
    IsIso (comparisonDirectImageCanonicalMate Λ u) := by
  exact isIso_comparisonDirectImagePlus Λ u

end AlgebraicGeometry.ProEtale
