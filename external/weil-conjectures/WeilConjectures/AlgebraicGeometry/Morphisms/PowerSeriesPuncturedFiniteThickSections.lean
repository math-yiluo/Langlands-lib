/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedThickeningRestriction
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables

/-! # Sections on a finite power-series thickening

## References

* Stacks Project, Tag 0EY9, the first displayed calculation
* Stacks Project, Tag 0EY9, the finite-index part of the first displayed calculation
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Restricting quotient power series to the punctured finite thickening is surjective. -/
theorem surjective_powerSeries_punctured_thickening_sections
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (n : ℕ) :
    let I : Ideal (MvPowerSeries (Fin d) A) := Ideal.span (Set.range MvPowerSeries.X)
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))
    Function.Surjective
      (((ΓSpecIso (.of (MvPowerSeries (Fin d) A ⧸ I ^ (n + 1)))).inv ≫
        (q ⁻¹ᵁ V).ι.appTop).hom) := by
  classical
  dsimp only
  let B := MvPowerSeries (Fin d) A
  let f := MvPowerSeries.constantCoeff (σ := Fin d) (R := A)
  have hI : RingHom.ker f =
      Ideal.span (Set.range (MvPowerSeries.X : Fin d → B)) := by
    exact (MvPowerSeries.quotient_first_variables_kernels A d 0 (Nat.zero_le d)).2
  rw [← hI]
  let q := FiniteEtale.Adic.baseMap f n
  let e := pullbackSymmetry V.ι q ≪≫ pullbackRestrictIsoRestrict q V
  have hfac : e.inv ≫ pullback.snd V.ι q = (q ⁻¹ᵁ V).ι := by
    simp [e]
  have he : Function.Surjective e.inv.appTop.hom := by
    exact (ConcreteCategory.bijective_of_isIso e.inv.appTop).2
  have hk := (bijective_powerSeries_punctured_thickening_restriction
    A hdepth d hd V hV n).2
  have hsurj := he.comp hk
  have hmap : (ΓSpecIso (.of (B ⧸ RingHom.ker f ^ (n + 1)))).inv ≫
      (pullback.snd V.ι q).appTop ≫ e.inv.appTop =
      (ΓSpecIso (.of (B ⧸ RingHom.ker f ^ (n + 1)))).inv ≫
        (q ⁻¹ᵁ V).ι.appTop := by
    rw [← Scheme.Hom.comp_appTop, hfac]
  change Function.Surjective
    (((ΓSpecIso (.of (B ⧸ RingHom.ker f ^ (n + 1)))).inv ≫
      (q ⁻¹ᵁ V).ι.appTop).hom)
  rw [← hmap]
  exact hsurj

end AlgebraicGeometry.Scheme
