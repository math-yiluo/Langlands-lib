/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.MvPowerSeriesFlat
import WeilConjectures.RingTheory.QuotientAssociatedPrimesFlatBaseChange
import WeilConjectures.RingTheory.MvPowerSeriesPrimeExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.AssociatedGermDetection
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.DepthLeDimAssociatedPrime

/-!
# Detecting sections at the punctured zero section

## References

* Stacks Project, Tag 0EY9, injectivity detail, expanded by Tags 0312 and 0311
* Stacks Project, Tag 0EY9, the omitted injectivity detail
* Tags 0312, 0BK4 and 0311
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A section on V vanishing as a germ at every point of the punctured zero
section is zero. -/
theorem eq_zero_of_powerSeries_punctured_germs
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (s : Γ(V.toScheme, ⊤))
    (hs : ∀ x :
      ((Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) ⁻¹ᵁ V).toScheme,
      (V.toScheme.presheaf.Γgerm
        ((Spec.map (CommRingCat.ofHom
          (MvPowerSeries.constantCoeff (σ := Fin d) (R := A))) ∣_ V) x)).hom s = 0) :
    s = 0 := by
  have _ := hd
  let B := MvPowerSeries (Fin d) A
  let z : Spec (.of A) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))
  let : Module.Flat A B :=
    RingHom.flat_algebraMap_iff.mp (MvPowerSeries.constants_flat A d)
  apply eq_zero_of_associated_germs B V s
  intro q hq hqa
  have hqa' : q.asIdeal ∈ associatedPrimes B (B ⧸ (⊥ : Ideal A).map
      (algebraMap A B)) := by
    rw [Ideal.map_bot]
    exact (AlgEquiv.quotientBot B B).toLinearEquiv.isAssociatedPrime_iff.mpr hqa
  obtain ⟨p, hp, hqp⟩ := associatedPrimes_quotient_map_of_flat A B ⊥ q.asIdeal hqa'
  have hpa : p ∈ associatedPrimes A A :=
    (AlgEquiv.quotientBot A A).toLinearEquiv.isAssociatedPrime_iff.mp hp
  have hpB : (p.map (algebraMap A B)).IsPrime := MvPowerSeries.isPrime_map_C A d p hpa.isPrime
  have heq : q.asIdeal = p.map (algebraMap A B) := by
    simpa only [hpB.radical] using hqp.eq_radical hpB.isPrimary
  let x : Spec (.of A) := ⟨p, hpa.isPrime⟩
  have hx : x ≠ IsLocalRing.closedPoint A := by
    intro hx
    have hpm : p = IsLocalRing.maximalIdeal A := congrArg PrimeSpectrum.asIdeal hx
    have hdim := IsLocalRing.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes p hpa
    let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
    rw [hpm, ringKrullDim_eq_zero_of_field] at hdim
    have hdepth' : (2 : WithBot ℕ∞) ≤ (IsLocalRing.depth (R := A) A : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr hdepth
    have h := hdepth'.trans hdim
    norm_num at h
  have hxV : z x ∈ V := (hV x).mpr hx
  have hspec : q ⤳ z x := by
    apply (PrimeSpectrum.le_iff_specializes _ _).mp
    change q.asIdeal ≤ (z x).asIdeal
    rw [heq]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change MvPowerSeries.constantCoeff (MvPowerSeries.C a) ∈ p
    simpa using ha
  let y : (z ⁻¹ᵁ V).toScheme := ⟨x, hxV⟩
  have hy : ((z ∣_ V) y : V.toScheme) = ⟨z x, hxV⟩ := by
    apply Subtype.ext
    exact congrArg (fun f : (z ⁻¹ᵁ V).toScheme ⟶ Spec (.of B) ↦ f y)
      (morphismRestrict_ι z V)
  have hzero : (V.toScheme.presheaf.Γgerm ⟨z x, hxV⟩).hom s = 0 := by
    have h := hs y
    change (V.toScheme.presheaf.Γgerm ((z ∣_ V) y)).hom s = 0 at h
    rwa [hy] at h
  have hspecV : (⟨q, hq⟩ : V.toScheme) ⤳ ⟨z x, hxV⟩ :=
    (subtype_specializes_iff _ _).mpr hspec
  change (V.toScheme.presheaf.germ ⊤ ⟨z x, hxV⟩ trivial).hom s = 0 at hzero
  have h := congrArg (fun f : Γ(V.toScheme, ⊤) ⟶
      V.toScheme.presheaf.stalk ⟨q, hq⟩ ↦ f.hom s)
    (V.toScheme.presheaf.germ_stalkSpecializes (U := ⊤) (by trivial) hspecV)
  simpa only [TopCat.Presheaf.Γgerm, CommRingCat.hom_comp, RingHom.comp_apply,
    hzero, map_zero] using h.symm

end AlgebraicGeometry.Scheme
