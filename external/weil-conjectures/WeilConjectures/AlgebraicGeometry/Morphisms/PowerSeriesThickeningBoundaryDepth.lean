/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesTruncatedFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Stalk

/-! # Boundary depth of a finite power-series thickening

## References

* Stacks Project, Tag 0EY9, finite-index calculation
* Stacks Project, Tag 0EY9, first displayed calculation, and Tag 0337
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The stalks outside the punctured part of a finite power-series thickening have
 depth at least two. -/
theorem powerSeries_thickening_boundary_depth
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (n : ℕ) :
    let Q := FiniteEtale.Adic.base
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n
    let q := FiniteEtale.Adic.baseMap
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n
    ∀ y : Q, y ∉ q ⁻¹ᵁ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := Q.presheaf.stalk y) (Q.presheaf.stalk y) := by
  dsimp only
  let B := MvPowerSeries (Fin d) A
  let f : B →+* A := MvPowerSeries.constantCoeff
  let I := RingHom.ker f
  let Q := B ⧸ I ^ (n + 1)
  let k : B →+* Q := Ideal.Quotient.mk _
  let c : A →+* B := MvPowerSeries.C
  let t : Spec (.of Q) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (k.comp c))
  have ht : Flat t := Flat.SpecMap_iff.mpr
    (MvPowerSeries.truncated_constants_flat A d n)
  change ∀ y : Spec (.of Q), y ∉ (Spec.map (CommRingCat.ofHom k)) ⁻¹ᵁ V →
    (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := (Spec (.of Q)).presheaf.stalk y) ((Spec (.of Q)).presheaf.stalk y)
  intro y hy
  have hker : I ≤ (PrimeSpectrum.comap k y).asIdeal := by
    intro b hb
    apply (PrimeSpectrum.comap k y).isPrime.mem_of_pow_mem (n + 1)
    change k (b ^ (n + 1)) ∈ y.asIdeal
    have hbpow : b ^ (n + 1) ∈ I ^ (n + 1) := Ideal.pow_mem_pow hb _
    rw [show k (b ^ (n + 1)) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hbpow]
    exact Ideal.zero_mem _
  have hf : Function.Surjective f := by
    intro a
    exact ⟨c a, MvPowerSeries.constantCoeff_C a⟩
  have hrange : PrimeSpectrum.comap k y ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective A f hf]
    exact hker
  obtain ⟨x, hx⟩ := hrange
  have htx : t y = x := by
    change PrimeSpectrum.comap (k.comp c) y = x
    rw [PrimeSpectrum.comap_comp_apply, ← hx, ← PrimeSpectrum.comap_comp_apply]
    have hfc : f.comp c = RingHom.id A := by
      ext a
      change MvPowerSeries.constantCoeff (MvPowerSeries.C a : B) = a
      exact MvPowerSeries.constantCoeff_C (σ := Fin d) a
    rw [hfc]
    rfl
  have hxy : (Spec.map (CommRingCat.ofHom f)) x =
      (FiniteEtale.Adic.baseMap f n) y := hx
  have hclosed : t y = IsLocalRing.closedPoint A := by
    rw [htx]
    by_contra hne
    apply hy
    change (FiniteEtale.Adic.baseMap f n) y ∈ V
    rw [← hxy]
    exact (hV x).mpr hne
  have : IsLocallyNoetherian (Spec (.of Q)) := by
    dsimp [Q, B, I, f]
    infer_instance
  have hbase : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := (Spec (.of A)).presheaf.stalk (t y))
      ((Spec (.of A)).presheaf.stalk (t y)) := by
    rw [hclosed]
    let e := stalkClosedPointIso (CommRingCat.of A)
    let φ := e.inv.hom
    have hbij : Function.Bijective φ := ConcreteCategory.bijective_of_isIso e.inv
    let : IsLocalHom φ := IsLocalHom.of_surjective φ hbij.2
    obtain ⟨_, hlocal, _, hd⟩ :=
      IsLocalRing.depth_eq_add_of_flat_local φ (RingHom.Flat.of_bijective hbij)
    rw [hd]
    exact hdepth.trans le_self_add
  obtain ⟨_, hlocal, _, hd⟩ :=
    IsLocalRing.depth_eq_add_of_flat_local (t.stalkMap y).hom (Flat.stalkMap t y)
  rw [hd]
  exact hbase.trans le_self_add

end AlgebraicGeometry.Scheme
