/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence

/-! # Proper factor of the restricted coefficient projection

The compact scalar map is definitionally the proper scalar mate followed by the
proper direct image of the open coefficient comparison. This is the first factor
in the proof of the restricted coefficient projection identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The compact scalar map factors through its proper scalar mate and the open
coefficient comparison. This is the proper-factor expansion used in the tensor
projection calculation (blueprint: lem-pur-etale-quotient-tensor-projection).

Proof: unfold `compactScalarMap` and the defining natural transformation
`ExceptionalCoefficients.compactSupportMap`; the displayed composite is exactly
its component at `K`. The statement is valid for identity and zero ring maps,
empty schemes, and identity compactifications because no cancellation or
invertibility is used.
-/
theorem compactScalarMap_proper_open_factor
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule C X) :
    (compactScalarMap a c).app K =
      (scalarMate a c.g).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K) ≫
        (lowerStar (ModuleCat.{u + 1} D) c.g).rightDerivedFunctor.map
          ((ExceptionalCoefficients.openIso a c.i).hom.app K) := by
  rfl

end AlgebraicGeometry.Etale
