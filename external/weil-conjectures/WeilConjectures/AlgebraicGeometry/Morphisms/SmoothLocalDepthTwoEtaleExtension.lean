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

import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity

/-!
# Extending a finite etale cover across a depth-two local fibre

## References

* Stacks Project, Tag 0EYB, Lemma 58.26.3, and Tag 0EY6, Lemma 58.21.5
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem maximal_smul_top_ne_top (R : Type*) [CommRing R] [IsLocalRing R] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
  rw [Ideal.smul_top_eq_map]
  change (IsLocalRing.maximalIdeal R).map (algebraMap R R) ≠ ⊤
  simpa only [Algebra.algebraMap_self, Ideal.map_id] using
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top

private theorem depth_le_of_ringEquiv {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A ≤ IsLocalRing.depth (R := B) B := by
  classical
  simp only [IsLocalRing.depth, Ideal.depth, maximal_smul_top_ne_top, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hmem a ha)

/-- A fibrewise dense open containing every nonclosed fibre admits finite etale extension. -/
theorem exists_finite_etale_extension_of_local_depth_two
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (U : L.Opens)
    (haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ U)
    (hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ U) :
      Set (q.fiber (IsLocalRing.closedPoint A))))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f] :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      ∃ e : (p ⁻¹ᵁ U).toScheme ≅ X, e.hom ≫ f = p ∣_ U := by
  have : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian q
  have hboundary : ∀ y : L, y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y) := by
    intro y hy
    have hqy : q y = IsLocalRing.closedPoint A := by
      by_contra hne
      exact hy (haway y hne)
    have hbase : (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec (.of A)).presheaf.stalk (q y))
        ((Spec (.of A)).presheaf.stalk (q y)) := by
      rw [hqy]
      let e : A ≃+* (Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A) :=
        (IsLocalization.atUnits A (IsLocalRing.maximalIdeal A).primeCompl
          (S := Localization.AtPrime (IsLocalRing.maximalIdeal A))
          (by
            intro x hx
            change IsUnit x
            simpa only [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal,
              mem_nonunits_iff, not_not] using hx)).toRingEquiv.trans
          (StructureSheaf.stalkIso A (IsLocalRing.closedPoint A)).toRingEquiv
      exact hdepth.trans (depth_le_of_ringEquiv e)
    obtain ⟨_, hlocal, _, hformula⟩ :=
      IsLocalRing.depth_eq_add_of_flat_local (q.stalkMap y).hom (Flat.stalkMap q y)
    rw [hformula]
    exact hbase.trans (le_add_right le_rfl)
  obtain ⟨E, p, hp, hE, e, he⟩ := exists_finite_extension_of_depth_two U hboundary f
  have : IsFinite p := hp
  have : Etale (p ∣_ U) := by
    rw [← he]
    infer_instance
  exact ⟨E, p, hp,
    etale_of_smooth_local_depth_two_finite_extension A q U haway hclosed hdepth p hE,
    e, he⟩

end AlgebraicGeometry.Scheme
