/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction

/-! # The injective Čech total complex is functorial

Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: def-pc-abelian-cech-total-map)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Apply the Čech functor degreewise, flip, and totalize a resolution map.
Source: Stacks Project, Tags 01EQ and 01FD, augmented comparison diagram.
(blueprint: def-pc-abelian-cech-total-map) -/
noncomputable def abelianCechTotalMap
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    (abelianCechDouble U I).total (.up ℕ) ⟶ (abelianCechDouble U J).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map
      (((TopCat.Sheaf.cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).map φ))
    (.up ℕ)

end AlgebraicGeometry.Scheme.Modules
