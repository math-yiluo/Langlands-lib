/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingResidueQuotientSurjective

/-! # Residue lifts for the completed comparison

## References

* Stacks Project, Tags 0BLH and 05ER
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

private theorem residue_lift_of_quotient_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (I : Ideal S)
    (h : Function.Surjective (fun a : R => Ideal.Quotient.mk I (g a))) :
    ∀ b : S, ∃ a : R, g a - b ∈ I := by
  intro b
  obtain ⟨a, ha⟩ := h (Ideal.Quotient.mk I b)
  refine ⟨a, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  exact sub_eq_zero.mpr ha

/-- Every completed section lifts modulo the extended maximal ideal. -/
theorem completedRingMap_residue_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    ∀ b : Γ(E, ⊤), ∃ a, D.completedRingMap a - b ∈
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)).map
        (((ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv ≫
          s.appTop).hom) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let I : Ideal (Γ(E, ⊤)) := (IsLocalRing.maximalIdeal C).map
    (((ΓSpecIso (.of C)).inv ≫ s.appTop).hom)
  have hq := D.completedRingMap_residue_quotient_surjective hU
  intro b
  exact residue_lift_of_quotient_surjective D.completedRingMap.hom I hq b

end AlgebraicGeometry.Scheme.CompletionGluingData
