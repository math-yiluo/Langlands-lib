/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict

import all WeilConjectures.AlgebraicGeometry.CoherentKernelConditionRestriction

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Finite type of a coherent module is preserved by restriction to every open.
Source: Stacks Project, Definitions 01BV and 01B5 and Lemma 01B6.
(blueprint: lem-weil-pbc-coherent-module-finite-type-local-restrict)
-/
theorem coherent_module_finite_type_local_restrict
    (X : Scheme.{u}) (F : X.Modules) :
    RingedSpace.IsCoherent X.toRingedSpace F →
      ∀ (W : X.Opens), ((Scheme.Modules.restrictFunctor W.ι).obj F).IsFiniteType := by
  intro hF W
  let : F.IsFiniteType := hF.1
  exact finiteType_restrict W.ι F

end AlgebraicGeometry
