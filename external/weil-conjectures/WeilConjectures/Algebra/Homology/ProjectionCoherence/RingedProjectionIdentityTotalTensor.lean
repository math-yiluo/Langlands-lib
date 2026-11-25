/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorTotalComponent

set_option linter.privateModule false

/-! # The identity comparison on ordinary total tensor complexes

Source: Stacks Project, Tags 03EL, 07A4 and 0FPI.
(blueprint: lem-sfb-ringed-projection-identity-total-tensor)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory MonoidalCategory
namespace SheafOfModules.ProjectionCoherence
open RingedTensor

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso

private noncomputable abbrev tensorTotal (X : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj ((@MonoidalCategory.curriedTensor X.mateModules _
    (monoidalCategory X.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

private theorem total_map_eq {A : Type*} [Category A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [CategoryTheory.Limits.HasCoproducts.{0} A]
    {P P' Q Q' : CochainComplex A ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))).map
          (Prod.mkHom a b) =
      HomologicalComplex.mapBifunctorMap a b (MonoidalCategory.curriedTensor A) (.up ℤ) := by
  simp [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

end SheafOfModules.ProjectionCoherence
