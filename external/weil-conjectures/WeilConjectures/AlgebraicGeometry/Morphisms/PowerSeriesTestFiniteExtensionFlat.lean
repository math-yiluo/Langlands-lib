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

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesFiniteEtaleExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness

/-!
# Flatness of a finite depth-two extension on a power-series spectrum

## References

* Stacks Project, Tag 0EYA and the last completion step of Tag 0EYB
* Tag 0EY6(2), (a), (b)
* Tag 0337
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite depth-two extension on a power-series spectrum is flat. -/
theorem flat_of_power_series_depth_two_finite_extension
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B)
    (n : ℕ) (hn : 0 < n)
    (V : (Spec (.of (MvPowerSeries (Fin n) B))).Opens)
    {F : Scheme.{u}} (r : F ⟶ Spec (.of (MvPowerSeries (Fin n) B)))
    [IsFinite r] [Etale (r ∣_ V)]
    (hboundary : ∀ w : F, r w ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk w) (F.presheaf.stalk w))
    (haway : ∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
      IsLocalRing.closedPoint B → v ∈ V)
    (hgeneric : ∃ v, v ∈ V ∧ v.asIdeal =
      (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n))) :
    Flat r := by
  obtain ⟨E, p, hp, het, hE, e, he⟩ :=
    exists_finite_etale_extension_of_power_series_open B hdepth n hn V haway hgeneric (r ∣_ V)
  have : IsFinite p := hp
  have : Etale p := het
  obtain ⟨i, hi⟩ := iso_of_finite_depth_two_extensions V r p hboundary hE e he
  rw [← hi]
  infer_instance

end AlgebraicGeometry.Scheme
