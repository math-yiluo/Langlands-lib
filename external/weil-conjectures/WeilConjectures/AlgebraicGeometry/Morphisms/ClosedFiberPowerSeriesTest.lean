/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothSectionPowerSeriesChart
import WeilConjectures.RingTheory.FlatLocalDepthFormula

/-!
# A flat power-series test through a closed boundary point

## References

* Stacks Project, Tag 0EYB, choice of a closed point and completion of a smooth chart
* Stacks Project, Tag 0EYB, proof from the residue extension to the sentence asserting that the
  extended maximal ideal maps into U
* Tags 07NE, 057G, 05D5, 00MB and 0337
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A closed boundary point admits a flat power-series test with a generic point in the open. -/
theorem exists_closed_fiber_power_series_test
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (U : L.Opens)
    (haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ U)
    (hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ U) :
      Set (q.fiber (IsLocalRing.closedPoint A))))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (x : q.fiber (IsLocalRing.closedPoint A)) (hx : IsClosed ({x} : Set _))
    (hout : q.fiberι (IsLocalRing.closedPoint A) x ∉ U) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B),
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B ∧
      ∃ (n : ℕ), 0 < n ∧
        ∃ (t : Spec (.of (MvPowerSeries (Fin n) B)) ⟶ L), Flat t ∧
          (∃ b, t b = q.fiberι (IsLocalRing.closedPoint A) x) ∧
          (∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
            IsLocalRing.closedPoint B → t v ∈ U) ∧
          ∃ v, t v ∈ U ∧ v.asIdeal =
            (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n)) := by
  obtain ⟨B, hB, hBl, hBn, φ, hφlocal, hφflat, hreflect, s, hs, hsx⟩ :=
    exists_smooth_closed_point_local_section A q x hx
  let := hB
  let := hBl
  let := hBn
  let := hφlocal
  obtain ⟨n, t, htflat, htq, hts, v, η, W, hv, htη, hW, hη⟩ :=
    exists_smooth_section_power_series_chart A q B φ hφflat s hs
  have hηU : q.fiberι (IsLocalRing.closedPoint A) η ∈ U := by
    obtain ⟨z, hzW, hzU⟩ := hclosed.inter_open_nonempty W W.isOpen hW
    exact (hη z hzW).mem_open (q.fiberι (IsLocalRing.closedPoint A) ⁻¹ᵁ U).isOpen hzU
  have hvU : t v ∈ U := by rwa [htη]
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    have hvb : v = (Spec.map
        (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin 0))))
        (IsLocalRing.closedPoint B) := by
      apply PrimeSpectrum.ext
      rw [hv]
      apply Ideal.comap_injective_of_surjective (MvPowerSeries.C (σ := Fin 0))
        MvPowerSeries.C_surjective
      rw [Ideal.comap_map_of_bijective _
        ⟨MvPowerSeries.C_injective, MvPowerSeries.C_surjective⟩]
      ext a
      change a ∈ IsLocalRing.maximalIdeal B ↔
        MvPowerSeries.constantCoeff (MvPowerSeries.C a) ∈ IsLocalRing.maximalIdeal B
      rw [MvPowerSeries.constantCoeff_C]
    exact hout (by rwa [hvb, hts, hsx] at hvU)
  obtain ⟨_, hfibre, _, hdepthB⟩ := IsLocalRing.depth_eq_add_of_flat_local φ hφflat
  let := hfibre
  refine ⟨B, hB, hBl, hBn, ?_, n, hn, t, htflat, ?_, ?_, v, hvU, hv⟩
  · rw [hdepthB]
    exact hdepth.trans (le_add_of_nonneg_right bot_le)
  · exact ⟨_, hts.trans hsx⟩
  · intro w hw
    apply haway
    intro heq
    have heq' : (Spec.map (CommRingCat.ofHom φ))
        ((Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) w) =
          IsLocalRing.closedPoint A := by
      rw [← Scheme.Hom.comp_apply, ← htq, Scheme.Hom.comp_apply]
      exact heq
    exact hw (hreflect _ heq')

end AlgebraicGeometry.Scheme
