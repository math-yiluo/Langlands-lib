/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.AlgebraicGeometry.SmoothProperQCohData
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option linter.unusedVariables false in
/-- Intermediate existence of the quasi-coherent and monoidal data used by the
projection comparison. Source: Stacks Project, Tag 0A9T.
(blueprint: lem-sc-smooth-proper-tensor-perfect-case-data). -/
theorem smoothProper_tensor_perfect_case_data
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings Y.toRingedSpace).over U))]
    (hTor : ∀ x : X, ∃ n : ℕ, ∀ (M : ModuleCat.{u} (Y.presheaf.stalk (f x))) (i : ℕ), n < i →
      IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (f x))) i).obj
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))).obj M)) :
    ∃ (hRf : ∀ E : schemeDerivedQCohCategory X,
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
      (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
      (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory X),
        schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj)),
      Nonempty (Functor.Monoidal (derivedPullback f)) ∧
      Nonempty (derivedPullback f ⊣ schemeDerivedDirectImage f) := by
  obtain ⟨hRf, hO, hTensor, _⟩ := smoothProper_qcoh_data f
  obtain ⟨m, _⟩ := exists_derivedPullbackMonoidalModel f
  obtain ⟨ha⟩ := nonempty_derivedPullbackAdjunction f
  exact ⟨hRf, hO, hTensor, ⟨m.toMonoidal⟩, ⟨ha⟩⟩
end AlgebraicGeometry
