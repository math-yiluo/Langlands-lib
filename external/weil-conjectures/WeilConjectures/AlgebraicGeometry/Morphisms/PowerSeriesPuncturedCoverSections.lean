/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedGlobalSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedThickeningSections
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Sections of finite étale covers and the power-series formal neighbourhood

## References

* Stacks Project, Tag 0EY9, structure-sheaf comparison, followed by Tag 0EKP, implication (1) to (3)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Sections of a single finite étale cover are recovered from compatible sections
on its quotient-power thickenings. -/
theorem finiteEtale_powerSeries_punctured_cover_sections_comparison
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (P : V.toScheme.FiniteEtale)
    (s : ∀ n : ℕ, Γ(FiniteEtale.Adic.cover
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n, ⊤))
    (hs : ∀ n, (FiniteEtale.Adic.coverTransition
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n).appTop
        (s (n + 1)) = s n) :
    ∃! a : Γ(P.obj.left, ⊤), ∀ n, (FiniteEtale.Adic.coverMap
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n).appTop a = s n := by
  have hglobal := bijective_powerSeries_punctured_globalSections A hdepth d hd V hV
  apply finiteEtale_adic_sections_comparison_of_structureSheaf
    (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V ?_ P s hs
  intro t ht
  obtain ⟨b, hb, huniq⟩ :=
    existsUnique_powerSeries_punctured_thickening_sections A hdepth d hd V hV t ht
  let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
  refine ⟨r b, ?_, ?_⟩
  · intro n
    exact hb n
  · intro a ha
    obtain ⟨c, rfl⟩ := hglobal.2 a
    have hc : ∀ n,
        ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop ≫
          (FiniteEtale.Adic.openThickeningMap
            (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V n).appTop) c = t n :=
      ha
    exact congrArg r (huniq c hc)

end AlgebraicGeometry.Scheme
