/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # The degree-zero comparison for sections on an open

Source: Stacks Project, Tag 01DZ, the definition of zeroth derived sections.
(blueprint: lem-sc-open-cohomology-zero-sections).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.RingedSpace

/-- Sections on an open preserve finite limits.
Source: Stacks Project, Tag 01DZ.
(blueprint: lem-sc-open-cohomology-zero-sections). -/
instance openModuleSections_preservesFiniteLimits (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteLimits (openModuleSections X U) := by
  unfold openModuleSections
  infer_instance

/-- The canonical comparison from zeroth derived sections to sections.
Source: Stacks Project, Tag 01DZ.
(blueprint: lem-sc-open-cohomology-zero-sections). -/
noncomputable def openCohomologyZeroSectionsIso (X : RingedSpace.{u}) (U : Opens X) :
    openModuleCohomology X 0 U ≅ openModuleSections X U :=
  letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  (openModuleSections X U).rightDerivedZeroIsoSelf

/-- The section comparison intertwines coefficient morphisms.
Source: Stacks Project, Tag 01DZ.
(blueprint: lem-sc-open-cohomology-zero-sections).

Proof: This is the naturality square of rightDerivedZeroIsoSelf. -/
theorem openCohomologyZeroSectionsIso_naturality (X : RingedSpace.{u}) (U : Opens X)
    {M N : SheafOfModules.{u} (moduleRings X)} (f : M ⟶ N) :
    (openModuleCohomology X 0 U).map f ≫ (openCohomologyZeroSectionsIso X U).hom.app N =
      (openCohomologyZeroSectionsIso X U).hom.app M ≫ (openModuleSections X U).map f :=
  (openCohomologyZeroSectionsIso X U).hom.naturality f

end AlgebraicGeometry.RingedSpace
