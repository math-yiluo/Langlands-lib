/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesLocalKernelCoefficients
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoPuncturedFunctionDetection
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-! # Detection of variable-ideal powers on the punctured zero section

## References

* Stacks Project, Tag 0EY9, first displayed calculation at a fixed index
* Stacks Project, the first displayed calculation at a fixed index, and the subsequent ring
  comparison
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Membership in a fixed power of the variables ideal is detected by germs
of the corresponding global section along the punctured zero section. -/
theorem powerSeries_mem_variables_pow_of_punctured_germs
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    let z := Spec.map
      (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
    let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
    ∀ (b : MvPowerSeries (Fin d) A) (n : ℕ),
      (∀ x : (z ⁻¹ᵁ V).toScheme,
        (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom (r b) ∈
          (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n) →
      b ∈ (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin d) (R := A)))) ^ n := by
  have _hd : 0 < d := hd
  dsimp only
  intro b n hb
  have hcoeff (E : Fin d →₀ ℕ) (hE : E.degree < n) : MvPowerSeries.coeff E b = 0 := by
    apply eq_zero_of_depth_two_punctured_germs A hdepth
    intro x hx
    let z := Spec.map
      (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
    have hxV : x ∈ z ⁻¹ᵁ V := (hV x).mpr hx
    let xU : (z ⁻¹ᵁ V).toScheme := ⟨x, hxV⟩
    exact powerSeries_low_coeff_germ_eq_zero_of_kernel_pow A d V b n xU (hb xU) E hE
  have hmem := (power_series_mem_combined_ideal_pow_iff A (⊥ : Ideal A) d n b).mpr
    (fun E hE ↦ by rw [hcoeff E hE]; exact Ideal.zero_mem _)
  simpa only [Ideal.map_bot, bot_sup_eq] using hmem

end AlgebraicGeometry.Scheme
