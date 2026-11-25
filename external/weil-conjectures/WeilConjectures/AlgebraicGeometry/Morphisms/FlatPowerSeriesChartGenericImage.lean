/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Fiber

import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import WeilConjectures.RingTheory.MvPowerSeriesQuotientKernel
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatBaseChangeClosedFiberGeneralizations

/-!
# Generic image of the extended maximal ideal under a flat power-series chart

## References

* Stacks Project, Tag 0EYB, the image of the extended maximal ideal
* Stacks Project, Tag 0EYB, the sentence about the image of the extended maximal ideal, with
  flatness of completion supplied by Tag 00MB
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The extended maximal ideal in a flat power-series chart maps to a generic point
of a component in an affine neighbourhood of the original closed fibre. -/
theorem exists_flat_power_series_chart_generic_image
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (n : ℕ) (t : Spec (.of (MvPowerSeries (Fin n) B)) ⟶
      Limits.pullback q (Spec.map (CommRingCat.ofHom φ))) [Flat t]
    (ht : t ≫ Limits.pullback.snd q (Spec.map (CommRingCat.ofHom φ)) =
      Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) :
    ∃ (v : Spec (.of (MvPowerSeries (Fin n) B)))
      (V : (q.fiber (IsLocalRing.closedPoint A)).Opens) (_ : IsAffineOpen V) (x : V),
      v.asIdeal = (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n)) ∧
      (t ≫ Limits.pullback.fst q (Spec.map (CommRingCat.ofHom φ))) v =
        q.fiberι (IsLocalRing.closedPoint A) (V.ι x) ∧
      closure ({x} : Set V) ∈ irreducibleComponents V := by
  classical
  let I := IsLocalRing.maximalIdeal B
  have : I.IsPrime := (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  have : IsDomain (B ⧸ I) := inferInstance
  have : IsDomain (MvPowerSeries (Fin n) (B ⧸ I)) :=
    NoZeroDivisors.to_isDomain _
  let ρ := MvPowerSeries.map (σ := Fin n) (Ideal.Quotient.mk I)
  have hker : RingHom.ker ρ = I.map MvPowerSeries.C :=
    MvPowerSeries.ker_map_quotient_of_fg (Fin n) I (IsNoetherian.noetherian I)
  let v : Spec (.of (MvPowerSeries (Fin n) B)) :=
    ⟨RingHom.ker ρ, RingHom.ker_isPrime ρ⟩
  have hv : v.asIdeal = I.map MvPowerSeries.C := hker
  have hvc : PrimeSpectrum.comap MvPowerSeries.C v = IsLocalRing.closedPoint B := by
    apply PrimeSpectrum.ext
    ext b
    change ρ (MvPowerSeries.C b) = 0 ↔ b ∈ I
    rw [MvPowerSeries.map_C]
    rw [← map_zero MvPowerSeries.C, MvPowerSeries.C_injective.eq_iff]
    exact Ideal.Quotient.eq_zero_iff_mem
  obtain ⟨η, hη, hlift⟩ := exists_closed_fiber_generalization_lifts
    A B (MvPowerSeries (Fin n) B) q φ MvPowerSeries.C t ht v hvc
  have hminimal : ∀ η', η' ⤳ η → η' = η := by
    intro η' hgen
    obtain ⟨w, hw, hwc, hwi⟩ := hlift η' hgen
    have hwle : w.asIdeal ≤ v.asIdeal := (PrimeSpectrum.le_iff_specializes w v).mpr hw
    have hvle : v.asIdeal ≤ w.asIdeal := by
      rw [hv]
      apply Ideal.map_le_iff_le_comap.mpr
      exact le_of_eq (congrArg PrimeSpectrum.asIdeal hwc).symm
    have hwv : w = v := PrimeSpectrum.ext (le_antisymm hwle hvle)
    apply (q.fiberι (IsLocalRing.closedPoint A)).isEmbedding.injective
    exact hwi.symm.trans (hwv ▸ hη)
  let V := ((q.fiber (IsLocalRing.closedPoint A)).affineCover.f
    ((q.fiber (IsLocalRing.closedPoint A)).affineCover.idx η)).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  let x : V := ⟨η, (q.fiber (IsLocalRing.closedPoint A)).affineCover.covers η⟩
  refine ⟨v, V, hV, x, hv, hη, ?_⟩
  obtain ⟨K, hK, hxK⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set V)) (isIrreducible_singleton.closure)
  obtain ⟨z, hz⟩ := QuasiSober.sober hK.1 (isClosed_of_mem_irreducibleComponents K hK)
  have hzx : z ⤳ x := hz.specializes (hxK (subset_closure (Set.mem_singleton x)))
  have hzx' : z = x := by
    apply Subtype.ext
    exact hminimal z.1 (hzx.map continuous_subtype_val)
  rw [← hzx', hz.def]
  exact hK

end AlgebraicGeometry.Scheme
