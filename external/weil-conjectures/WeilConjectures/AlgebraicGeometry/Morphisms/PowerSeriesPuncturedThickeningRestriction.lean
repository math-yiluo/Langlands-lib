/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedRestrictionIso

/-!
# Restriction to a punctured power-series thickening

## References

* Stacks Project, Tag 0EY9, first displayed calculation at a fixed index
* Stacks Project, Tag 0EY9, first displayed calculation, and Tag 0BK0
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Sections of each individual thickening are its quotient ring. -/
theorem bijective_powerSeries_punctured_thickening_restriction
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (n : ℕ) :
    Function.Bijective
      ((ΓSpecIso (.of (MvPowerSeries (Fin d) A ⧸ FiniteEtale.Adic.ideal
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n))).inv ≫
        (pullback.snd V.ι (FiniteEtale.Adic.baseMap
          (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n)).appTop).hom := by
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (isIso_powerSeries_punctured_thickening_restriction A hdepth d hd V hV n)

end AlgebraicGeometry.Scheme
