/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapKernelTorsion
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapTorsionKernel

/-! # Injectiveity of completed matching sections

## References

* Stacks Project, Tag 05ER, kernel argument
* Tags 0BLH and 05EU
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The completed matching-ring comparison is injective. -/
theorem completedRingMap_injective
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    Function.Injective D.completedRingMap := by
  apply (injective_iff_map_eq_zero D.completedRingMap.hom).mpr
  intro x hx
  obtain ⟨n, hn⟩ := D.completedRingMap_kernel_torsion hU x hx
  exact D.completedRingMap_torsion_kernel_zero hU x n hn hx

end AlgebraicGeometry.Scheme.CompletionGluingData
