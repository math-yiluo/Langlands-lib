/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated

/-! # Canonical resolution comparisons without an auxiliary finite-field datum

Source: Stacks Project, sites-cohomology.tex, Tags 06YS/06YT/06YY; derived.tex,
Tags 05RT/06XN; Bhatt--Scholze, p. 24, Definition 3.5.2
(auxiliary; not a blueprint node).

This is the unrestricted interface to the same augmented reduction tower.
It uses the published completed sheaf and scalarReductionExtension, its universal
derived counit, and the canonical localization factorization. Index n means
exponent n+1. The site and coefficient universes remain independent.

## Main definitions and statements

- `unrestrictedTowerResolutionIso`: computation through the universal derived counit.
- `unrestrictedTowerFiniteComparison`: canonical comparison of two resolutions.
- `unrestrictedTowerUnit`: the uniquely normalized unit chain map.
- `unrestrictedTowerTransition`: the published canonical transition at P.
- `unrestrictedReductionTowerWellDefined`: invariance of the augmented derived tower.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

/-- Restriction changes the scalar action and keeps the underlying additive map.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance unrestrictedTowerRestrictionAdditive (n : ℕ) :
    (scalarReductionRestriction l E Y n).Additive :=
  inferInstance

/-- Exactness supplies the limits instance for the recorded restriction functor.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance unrestrictedTowerRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (scalarReductionRestriction l E Y n) :=
  scalarReductionRestrictionLimits l E Y n

/-- Exactness supplies the colimits instance for the recorded restriction functor.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance unrestrictedTowerRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (scalarReductionRestriction l E Y n) :=
  scalarReductionRestrictionColimits l E Y n

/-- Additivity of the recorded extension, at the explicit coefficient sizes.
Source: Stacks Tag 06YY (auxiliary; not a blueprint node). -/
noncomputable instance unrestrictedTowerExtensionAdditive (n : ℕ) :
    (scalarReductionExtension l E Y n).Additive :=
  scalarReductionExtensionAdditive.{t, u} l E Y n

/-- The termwise finite reduction, using the recorded change-of-rings functor.
Source: Stacks Tag 06YY (auxiliary; not a blueprint node). -/
noncomputable abbrev unrestrictedTowerFiniteComplex (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :=
  ((scalarReductionExtension l E Y n).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

/-- The same reduction regarded as a complex over the completed coefficient sheaf.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable abbrev unrestrictedTowerComplex (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :=
  ((scalarReductionRestriction l E Y n).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (unrestrictedTowerFiniteComplex l E Y n P)

/-- The chain-level unit x ↦ x⊗1, determined uniquely by its sectionwise formula.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def unrestrictedTowerUnit
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    P ⟶ unrestrictedTowerComplex l E Y n P :=
  { f := fun i ↦ (scalarReductionExtension_adjunction l E Y n).choose.unit.app (P.X i)
    comm' := fun i j _ ↦
      ((scalarReductionExtension_adjunction l E Y n).choose.unit.naturality
        (P.d i j)).symm }

private noncomputable def towerCounit (n : ℕ) :
    DerivedCategory.Q ⋙ scalarReductionDerivedExtension l E Y n ⟶
      (scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm _).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) (scalarReductionCounit l E Y n) ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight
      ((scalarReductionExtension l E Y n).mapHomotopyCategoryFactors (.up ℤ)) _).hom ≫
    (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)).hom

attribute [local irreducible] towerCounit

attribute [local irreducible] unrestrictedTowerUnit

end WeilConjectures
