/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction

/-! # Section complexes of injective resolutions are functorial

Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: def-pc-abelian-cech-sections-map)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Apply global sections degreewise to a resolution cochain map.
Source: Stacks Project, Tag 01EQ, section complexes.
(blueprint: def-pc-abelian-cech-sections-map) -/
noncomputable def abelianCechSectionsMap
    {X : Scheme.{u}} {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) : abelianCechSections I ⟶ abelianCechSections J :=
  ((sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens))).mapHomologicalComplex
    (.up ℕ)).map φ

end AlgebraicGeometry.Scheme.Modules
