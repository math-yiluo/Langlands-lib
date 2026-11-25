/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.ProperFlatStructureSheafStalkInjective
import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatStructureSheafStalkSurjective

/-!
# A single-fibre criterion for the structure-sheaf unit on a stalk

## References

* Stacks Project, Tag 0E62, proof, localized at one point
* Stacks Project, Tag 0E62, proof
* Stacks Project, Tag 0BCD
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If the canonical functions map on one fibre is an isomorphism, the ordinary module
adjunction unit is bijective at that point of the base. No hypothesis on the functions
of the other fibres, and no assertion about arbitrary base change, is made here.
-/
theorem bijective_structureSheafMap_stalk_of_proper_flat_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (s : S)
    (hs : IsIso (f.fiberToSpecResidueField s).appTop) :
    Function.Bijective
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)).stalkLinearMap s) := by
  constructor
  · exact injective_structureSheafMap_stalk_of_proper_flat_fiber f s hs
  · exact surjective_structureSheafMap_stalk_of_proper_flat_fiber f s hs

end AlgebraicGeometry
