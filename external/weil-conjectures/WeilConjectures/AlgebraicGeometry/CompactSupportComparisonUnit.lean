/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # The comparison unit in fixed-coefficient module sheaves

Source: the blueprint, chap-Proper-base-change, theorem-bounded-below-cohomology-comparison;
Stacks Project, Tag 099V (blueprint: theorem-bounded-below-cohomology-comparison).

This exposes the canonical unit in the fixed-ring presentation used by compact support.
The recorded coefficient realization identifies this presentation with constant-ring
module sheaves. The proof uses the existing generic injective-acyclicity criterion
for the canonical bounded-below derived adjunction unit.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The actual bounded below comparison-adjunction unit is invertible on all objects.
Source: Stacks, Tag 099V; blueprint site-comparison theorem
(blueprint: theorem-bounded-below-cohomology-comparison).

Proof: resolve a bounded below complex by a bounded below complex of injectives.
The ordinary comparison unit is invertible termwise, and comparison inverse image
sends injectives to direct-image-acyclic objects. Thus the right-derived comparison
on this complex is invertible. Their composite is the canonical derived unit.
Naturality transports invertibility from this representative to every bounded below
object and assembles its inverses into a natural isomorphism. The adjunction Hom
bijection, followed by composition with this unit, gives full faithfulness. This is
the same six-step injective-resolution proof as the realized-coefficient statement;
no condition on the individual module sheaves is imposed. -/
theorem isIso_compactSupportComparisonUnit (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    IsIso (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) T).unit := by
  have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} Λ) T
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  change IsIso
    ((comparisonAdjunction (ModuleCat.{u + 1} Λ) T).derivedAdjunctionPlus.unit.app M)
  rw [(comparisonAdjunction (ModuleCat.{u + 1} Λ) T).derivedAdjunctionPlus_eq_derivedPlus]
  exact (comparisonAdjunction (ModuleCat.{u + 1} Λ) T).isIso_derivedPlus_unit_app_of_rightAcyclic
    (fun _ _ ↦ inferInstance)
    (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective (ModuleCat.{u + 1} Λ) T I) M

end AlgebraicGeometry.ProEtale
