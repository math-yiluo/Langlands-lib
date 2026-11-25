/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedAdjointLift
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedTensorLift
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedCompositionComparison
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedIdentityComparison
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedTwoIsoComparison
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Existence of normalized derived monoidal comparisons on ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D, 07A6, 0D6E, 0FPI.
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem tensor_model (X : Site.{u, w}) :
    ∃ r : RingedTensorModel X.corner, ∀ P Q hP hQ,
      r.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom := by
  let ι : ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
        (J := X.J) (R := X.A)) := {
    obj := fun P ↦ ⟨P.obj,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
    map := fun a ↦ ObjectProperty.homMk a.hom }
  let r : RingedTensorModel X.corner := {
    representative := Functor.isoWhiskerLeft (ι.prod ι) X.model.comparison }
  exact ⟨r, fun _ _ _ _ ↦ rfl⟩

end CategoryTheory.RingedDerivedComparisons
