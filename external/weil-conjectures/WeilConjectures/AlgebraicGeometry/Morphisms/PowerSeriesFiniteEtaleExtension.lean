/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.MvPowerSeriesFlat
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesDepthTwoBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleDescentNearClosedPoint

/-!
# Extending finite etale covers of a power-series open

## References

* Stacks Project, Tag 0EYA, with the boundary depth calculation of Tag 0337
* Tag 0EY6(1), (2), (a), (b)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite etale cover of the indicated power-series open extends to a finite
etale cover, with depth at least two above the complement. -/
theorem exists_finite_etale_extension_of_power_series_open
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B)
    (n : ℕ) (hn : 0 < n)
    (V : (Spec (.of (MvPowerSeries (Fin n) B))).Opens)
    (haway : ∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
      IsLocalRing.closedPoint B → v ∈ V)
    (hgeneric : ∃ v, v ∈ V ∧ v.asIdeal =
      (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n)))
    {X : Scheme.{u}} (f : X ⟶ V.toScheme) [IsFinite f] [Etale f] :
    ∃ (E : Scheme.{u}) (p : E ⟶ Spec (.of (MvPowerSeries (Fin n) B))),
      IsFinite p ∧ Etale p ∧
      (∀ z : E, p z ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ V).toScheme ≅ X, e.hom ≫ f = p ∣_ V := by
  let t := Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n) (R := B)))
  have : Flat t := Flat.SpecMap_iff.mpr (MvPowerSeries.constants_flat B n)
  have hboundary : ∀ y : Spec (.of (MvPowerSeries (Fin n) B)), y ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec (.of (MvPowerSeries (Fin n) B))).presheaf.stalk y)
        ((Spec (.of (MvPowerSeries (Fin n) B))).presheaf.stalk y) := by
    intro y hy
    have hty : t y = IsLocalRing.closedPoint B := by
      by_contra hne
      exact hy (haway y hne)
    have hbase : (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec (.of B)).presheaf.stalk (t y))
        ((Spec (.of B)).presheaf.stalk (t y)) := by
      rw [hty]
      let e : B ≃+* (Spec (.of B)).presheaf.stalk (IsLocalRing.closedPoint B) :=
        (IsLocalization.atUnits B (IsLocalRing.maximalIdeal B).primeCompl
          (S := Localization.AtPrime (IsLocalRing.maximalIdeal B)) (by
            intro x hx
            change IsUnit x
            simpa only [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal,
              mem_nonunits_iff, not_not] using hx)).toRingEquiv.trans
          (StructureSheaf.stalkIso B (IsLocalRing.closedPoint B)).toRingEquiv
      let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
      obtain ⟨_, hlocal, _, hedepth⟩ :=
        IsLocalRing.depth_eq_add_of_flat_local e.toRingHom
          (RingHom.Flat.of_bijective e.bijective)
      rw [hedepth]
      exact hdepth.trans le_self_add
    obtain ⟨_, hlocal, _, hd⟩ :=
      IsLocalRing.depth_eq_add_of_flat_local (t.stalkMap y).hom (Flat.stalkMap t y)
    rw [hd]
    exact hbase.trans le_self_add
  obtain ⟨E, p, hp, hE, e, he⟩ := exists_finite_extension_of_depth_two V hboundary f
  have : IsFinite p := hp
  have : Etale (p ∣_ V) := by
    rw [← he]
    infer_instance
  have hpet : Etale p := by
    by_cases hV : V = ⊤
    · apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale)
        (fun _ : Unit ↦ V) (by simp [hV])
      exact fun _ ↦ inferInstance
    · obtain ⟨Y, g, a, hg, H⟩ :=
        exists_finite_base_of_power_series_depth_two B hdepth n hn V hV haway p hE
      have : IsFinite g := hg
      obtain ⟨v, hv, hideal⟩ := hgeneric
      have hclosed : t v = IsLocalRing.closedPoint B := by
        apply PrimeSpectrum.ext
        change v.asIdeal.comap (MvPowerSeries.C (σ := Fin n)) =
          IsLocalRing.maximalIdeal B
        rw [hideal]
        exact Ideal.comap_map_eq_self_of_isMaximal _ (hideal ▸ v.isPrime.ne_top)
      have : Etale g :=
        etale_of_flat_base_change_near_closed_point B g t a p H V v hv hclosed
      exact MorphismProperty.of_isPullback (P := @Etale) H inferInstance
  exact ⟨E, p, hp, hpet, hE, e, he⟩

end AlgebraicGeometry.Scheme
