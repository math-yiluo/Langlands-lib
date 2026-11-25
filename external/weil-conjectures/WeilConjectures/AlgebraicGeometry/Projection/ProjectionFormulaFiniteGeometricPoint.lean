/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaTriangleClosure
import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

set_option linter.privateModule false

/-! # Proper projection formula over a geometric point

## References

* Stacks Project, Tags 0F0G and 0F12
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

open Scheme
variable (Λ : Type (u + 1)) [CommRing Λ]
variable (k : Type u) [Field k] [IsAlgClosed k]
private lemma constantCounit (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((constantSheafAdj (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal).counit.app F) := by
  let J := (Spec (.of k)).smallEtaleTopology
  let U := CategoryTheory.forget (ModuleCat.{u + 1} Λ)
  let G := (sheafCompose J U).obj F
  have : IsIso ((constantSheafAdj J (Type (u + 1)) terminalIsTerminal).counit.app G) :=
    (Scheme.spec_algClosed_etale_sheaf_constant k G).1
  have : IsIso ((sheafCompose J U).map
      ((constantSheafAdj J (ModuleCat.{u + 1} Λ) terminalIsTerminal).counit.app F)) := by
    rw [← constantSheafAdj_counit_w J U F terminalIsTerminal]
    infer_instance
  exact isIso_of_reflects_iso _ (sheafCompose J U)

section CoproductFunctors
universe v
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

end CoproductFunctors

end AlgebraicGeometry.Etale
