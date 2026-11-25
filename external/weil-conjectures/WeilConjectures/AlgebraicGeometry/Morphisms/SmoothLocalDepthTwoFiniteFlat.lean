/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat

/-!
# Flatness of a finite depth-two extension on a smooth local scheme

## References

* Stacks Project, Tag 0EYB, formal completion step
* Stacks Project, formal completion step, with Tags 0EYA and 0EY6(2), (a), (b)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Let `L` be smooth over a Noetherian local ring `A` of depth at least two and let `U ⊆ L` be
an open containing all points off the closed fibre and dense in the closed fibre. A finite
morphism `E ⟶ L` that is étale over `U` and has depth at least two at the points over the
complement of `U` is flat. -/
theorem flat_of_smooth_local_depth_two_finite_extension
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (U : L.Opens)
    (haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ U)
    (hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ U) :
      Set (q.fiber (IsLocalRing.closedPoint A))))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ U)]
    (hboundary : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    Flat p := by
  classical
  have : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian q
  let F : Set L := {y | ∀ z : E, p z = y → (p.stalkMap z).hom.Flat}
  have hF : IsOpen F := isOpen_setOf_finite_flat_stalks p
  have hUF : (U : Set L) ⊆ F := by
    intro y hy z hz
    let zU : (p ⁻¹ᵁ U).toScheme := ⟨z, by change p z ∈ U; rwa [hz]⟩
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p U zU)).mp (Flat.stalkMap (p ∣_ U) zU)
  let B : Set (q.fiber (IsLocalRing.closedPoint A)) :=
    (q.fiberι (IsLocalRing.closedPoint A)) ⁻¹' Fᶜ
  have hB : IsClosed B := hF.isClosed_compl.preimage (q.fiberι _).continuous
  have hBempty : B = ∅ := by
    by_contra hne
    obtain ⟨x, hxB, hxclosed⟩ := nonempty_inter_closedPoints
      (Set.nonempty_iff_ne_empty.mpr hne) hB.isLocallyClosed
    have hxU : q.fiberι (IsLocalRing.closedPoint A) x ∉ U := by
      intro hxU
      exact hxB (hUF hxU)
    apply hxB
    intro z hz
    exact flat_stalk_of_smooth_local_depth_two_closed_fiber A q U haway hclosed hdepth
      p hboundary x hxclosed hxU z hz
  apply Flat.of_stalkMap
  intro z
  have hpz : p z ∈ F := by
    by_cases hy : q (p z) = IsLocalRing.closedPoint A
    · let x := (q.fiberHomeo (IsLocalRing.closedPoint A)).symm ⟨p z, hy⟩
      have hx : q.fiberι (IsLocalRing.closedPoint A) x = p z :=
        q.fiberι_fiberHomeo_symm _ _
      by_contra hnot
      have hxB : x ∈ B := by
        change q.fiberι (IsLocalRing.closedPoint A) x ∉ F
        rwa [hx]
      rw [hBempty] at hxB
      exact hxB
    · exact hUF (haway (p z) hy)
  exact hpz z rfl


end AlgebraicGeometry.Scheme
