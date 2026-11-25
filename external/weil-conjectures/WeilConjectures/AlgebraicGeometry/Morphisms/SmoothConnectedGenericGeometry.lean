/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryStalkIso

/-!
# Geometry of a nonempty smooth geometrically connected family

## References

* Stacks Project, Tags 034F, 056T and 01UA
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A nonempty smooth geometrically connected family over a normal integral base
and its generic fibre are normal integral with the same function field. -/
theorem smooth_connected_generic_geometry {S C : Scheme.{u}} [IsIntegral S]
    [Nonempty C] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c) :
    ∃ hC : IsIntegral C, letI := hC;
      ∃ hη : IsIntegral Cη, letI := hη;
        (∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)) ∧
        (∀ x : Cη, IsIntegrallyClosed (Cη.presheaf.stalk x)) ∧
        ∃ e : Spec C.functionField ≅ Spec Cη.functionField,
          (e.hom ≫ Cη.fromSpecStalk (genericPoint Cη)) ≫ j =
            C.fromSpecStalk (genericPoint C) := by
  obtain ⟨hC, hη, hnC, hnη⟩ := smooth_connected_generic_geometry_core hS c q j hCη
  let := hC
  let := hη
  obtain ⟨e, he⟩ := smooth_connected_generic_geometry_stalk_iso c q j hCη
  exact ⟨hC, hη, hnC, hnη, e, he⟩

end AlgebraicGeometry.Scheme
