/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse

/-!
# Commutative continuous coefficient rings in the scheme universe

This interface completes the universe repair of `ContinuousCoefficientUniverse` by exporting
commutativity for a commutative coefficient ring, together with the existing condensed module
operations. The underlying coefficient sheaf and its pointwise operations are unchanged.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Profinite

variable (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- Pointwise multiplication makes continuous commutative coefficients a commutative ring object.
Source: the existing `Profinite.isCommMonObj_continuousMapRingObj`, with the coefficient carrier
in the scheme universe rather than Type 0.
(auxiliary; not a blueprint node). -/
instance isCommMonObj_continuousCoefficientRingObj :
    IsCommMonObj (continuousCoefficientRingObj T) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (continuousCoefficientRingSheaf T) fun S (a b : ULift.{u + 1} C(S.unop, T)) ↦ mul_comm a b

end Profinite
