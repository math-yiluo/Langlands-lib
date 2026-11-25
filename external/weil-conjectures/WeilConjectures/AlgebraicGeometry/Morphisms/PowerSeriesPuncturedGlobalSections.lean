/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFormalApproximation
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedGermDetection
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Filtration

/-!
# Global sections of a power-series open containing the punctured zero section

## References

* Stacks Project, Tag 0EY9, first displayed comparison in the proof
* Stacks Project, the comparison of global sections preceding the finite locally free argument
* Tags 0BK0, 0EKP and 0EL8 supply Hartogs and the uniqueness argument
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The canonical restriction from the power-series ring to the global sections of
an open containing precisely the punctured zero section is bijective. -/
theorem bijective_powerSeries_punctured_globalSections
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    Function.Bijective
      ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom := by
  let z := Spec.map
    (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
  let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
  have happrox := existsUnique_powerSeries_punctured_formal_approximation
    A hdepth d hd V hV
  dsimp only at happrox
  have hzero (s : Γ(V.toScheme, ⊤))
      (hs : ∀ (x : (z ⁻¹ᵁ V).toScheme) (n : ℕ),
        (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom s ∈
          (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n) : s = 0 := by
    apply eq_zero_of_powerSeries_punctured_germs A hdepth d hd V hV s
    intro x
    let J := RingHom.ker ((z ∣_ V).stalkMap x).hom
    have hJ : J ≠ ⊤ := RingHom.ker_ne_top _
    have hm : (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom s ∈ ⨅ n : ℕ, J ^ n :=
      Ideal.mem_iInf.mpr (hs x)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing J hJ] at hm
    exact hm
  constructor
  · intro a b hab
    obtain ⟨c, _, huniq⟩ := happrox (r a)
    have ha : ∀ (x : (z ⁻¹ᵁ V).toScheme) (n : ℕ),
        (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom (r a - r a) ∈
          (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n := by
      intro x n
      simp only [sub_self, map_zero, Ideal.zero_mem]
    have hb : ∀ (x : (z ⁻¹ᵁ V).toScheme) (n : ℕ),
        (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom (r a - r b) ∈
          (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n := by
      intro x n
      rw [show r a = r b from hab, sub_self, map_zero]
      exact Ideal.zero_mem _
    exact (huniq a ha).trans (huniq b hb).symm
  · intro s
    obtain ⟨b, hb, _⟩ := happrox s
    exact ⟨b, (sub_eq_zero.mp (hzero (s - r b) hb)).symm⟩

end AlgebraicGeometry.Scheme
