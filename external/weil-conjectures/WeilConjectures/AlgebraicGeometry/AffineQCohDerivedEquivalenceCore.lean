/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedAdjunctionConstruction
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedAdjunctionUnitCounit
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedTildeTriangulated

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- Core affine derived equivalence data, omitting the normalization on shifts.
Source: Stacks Project, Derived Categories of Schemes, Lemma 36.3.5, Tag 06Z0
(blueprint: new-affine-qcoh-derived-equivalence-core).
The proof constructs the derived tilde/global-sections equivalence using exactness of
termwise tilde, affine acyclicity, and the unit and counit quasi-isomorphisms. -/
theorem exists_affineQCohDerivedEquivalence_core (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    ∃ e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory (Spec (.of A)),
      Nonempty (DerivedCategory.Q ⋙ e.functor ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) ∧
      Nonempty (e.inverse ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor) ∧
      (∃ (_h : (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).CommShift ℤ),
        (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).IsTriangulated) := by
  obtain ⟨F, G, ⟨adj⟩, hF, hG⟩ := affineQCohDerivedAdjunction_construction A
  obtain ⟨hunit, hcounit⟩ := affineQCohDerivedAdjunction_unit_counit A F G adj hF hG
  let : ∀ M, IsIso (adj.unit.app M) := hunit
  let : ∀ K, IsIso (adj.counit.app K) := hcounit
  obtain ⟨hs, ht⟩ := affineQCohDerivedEquivalence_core_triangulated A F hF
  exact ⟨adj.toEquivalence, hF, hG, ⟨hs, ht⟩⟩

end AlgebraicGeometry
