/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Data.Finsupp.Weight
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-! # Coefficients of power-series germs modulo the zero-section ideal

## References

* Stacks Project, Tag 0EY9, fixed-index thickening calculation
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem localized_low_coefficients
    (A : Type u) [CommRing A] (d : ℕ) (p : PrimeSpectrum A)
    (b : MvPowerSeries (Fin d) A) (n : ℕ)
    (hb : algebraMap (MvPowerSeries (Fin d) A)
      (Localization.AtPrime (p.comap (MvPowerSeries.constantCoeff
        (σ := Fin d) (R := A))).asIdeal) b ∈
      (RingHom.ker (Localization.localRingHom
        (p.comap (MvPowerSeries.constantCoeff (σ := Fin d) (R := A))).asIdeal p.asIdeal
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) rfl)) ^ n) :
    ∀ E : Fin d →₀ ℕ, E.degree < n →
      algebraMap A (Localization.AtPrime p.asIdeal) (MvPowerSeries.coeff E b) = 0 := by
  classical
  let q := p.comap (MvPowerSeries.constantCoeff (σ := Fin d) (R := A))
  let T := Localization.AtPrime p.asIdeal
  let f := MvPowerSeries.map (σ := Fin d) (algebraMap A T)
  have hu (s : q.asIdeal.primeCompl) : IsUnit (f s) := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    exact IsLocalization.map_units (M := p.asIdeal.primeCompl) T
      ⟨MvPowerSeries.constantCoeff s.1, s.2⟩
  let l : Localization.AtPrime q.asIdeal →+* MvPowerSeries (Fin d) T :=
    IsLocalization.lift hu
  let c := Localization.localRingHom q.asIdeal p.asIdeal
    (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) rfl
  have hc : (MvPowerSeries.constantCoeff (σ := Fin d) (R := T)).comp l = c := by
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    ext a
    simp only [RingHom.comp_apply, l, f, IsLocalization.lift_eq,
      MvPowerSeries.constantCoeff_map, c]
    exact (Localization.localRingHom_to_map q.asIdeal p.asIdeal
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) rfl a).symm
  let I : Ideal (MvPowerSeries (Fin d) T) := Ideal.span (Set.range MvPowerSeries.X)
  have hker : RingHom.ker c ≤ I.comap l := by
    intro a ha
    have hz : MvPowerSeries.constantCoeff (l a) = 0 := by
      exact (RingHom.congr_fun hc a).trans ha
    have hmem := (power_series_mem_combined_ideal_pow_iff T (⊥ : Ideal T) d 1 (l a)).mpr
      (fun E hE ↦ by
        have hE0 : E = 0 := (Finsupp.degree_eq_zero_iff E).mp (by omega)
        subst E
        simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff, hz] using
          (Ideal.zero_mem ((⊥ : Ideal T) ^ (1 - (0 : Fin d →₀ ℕ).degree))))
    change l a ∈ I
    simpa only [Ideal.map_bot, bot_sup_eq, pow_one] using hmem
  have hpow : l (algebraMap _ (Localization.AtPrime q.asIdeal) b) ∈ I ^ n :=
    (le_trans (pow_le_pow_left' hker n) (Ideal.le_comap_pow l n)) hb
  have hf : f b ∈ I ^ n := by simpa only [l, IsLocalization.lift_eq] using hpow
  have hcoeff := (power_series_mem_combined_ideal_pow_iff T (⊥ : Ideal T) d n (f b)).mp
    (by simpa only [Ideal.map_bot, bot_sup_eq] using hf)
  intro E hE
  have he := hcoeff E hE
  simpa only [f, MvPowerSeries.coeff_map, Ideal.bot_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hE)),
    Ideal.mem_bot]
    using he

set_option backward.isDefEq.respectTransparency false in
/-- Local membership in a zero-section kernel power kills each lower coefficient
in the corresponding base stalk. -/
theorem powerSeries_low_coeff_germ_eq_zero_of_kernel_pow
    (A : Type u) [CommRing A] (d : ℕ)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens) :
    let z := Spec.map
      (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
    let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
    ∀ (b : MvPowerSeries (Fin d) A) (n : ℕ) (x : (z ⁻¹ᵁ V).toScheme),
      (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom (r b) ∈
        (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n →
      ∀ E : Fin d →₀ ℕ, E.degree < n →
        ((Spec (.of A)).presheaf.Γgerm ((z ⁻¹ᵁ V).ι x)).hom
          ((ΓSpecIso (.of A)).inv.hom (MvPowerSeries.coeff E b)) = 0 := by
  classical
  dsimp only
  intro b n x hb E hE
  let z := Spec.map
    (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
  let p : PrimeSpectrum A := (z ⁻¹ᵁ V).ι x
  let c := CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A))
  let α := morphismRestrictStalkMap z V x ≪≫ Scheme.arrowStalkMapSpecIso c p
  let j := α.hom.left.hom
  let k := α.hom.right.hom
  let l := Localization.localRingHom
    (p.comap (MvPowerSeries.constantCoeff (σ := Fin d) (R := A))).asIdeal p.asIdeal
    (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) rfl
  have hj : RingHom.ker ((z ∣_ V).stalkMap x).hom ≤ (RingHom.ker l).comap j := by
    intro a ha
    change l (j a) = 0
    have hw := RingHom.congr_fun (congrArg CommRingCat.Hom.hom α.hom.w) a
    change l (j a) = k (((z ∣_ V).stalkMap x).hom a) at hw
    rw [hw, show ((z ∣_ V).stalkMap x).hom a = 0 from ha, map_zero]
  have hm := (le_trans (pow_le_pow_left' hj n) (Ideal.le_comap_pow j n)) hb
  have hmap : j ((V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom
      (((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom b)) =
      algebraMap (MvPowerSeries (Fin d) A)
        (Localization.AtPrime
          (p.comap (MvPowerSeries.constantCoeff (σ := Fin d) (R := A))).asIdeal) b := by
    change (((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop ≫
      V.toScheme.presheaf.Γgerm ((z ∣_ V) x) ≫ α.hom.left).hom b) = _
    simp only [α, morphismRestrictStalkMap, Scheme.arrowStalkMapSpecIso,
      Iso.trans_hom, Arrow.comp_left, Arrow.isoMk', Arrow.isoMk_hom_left,
      Category.assoc, TopCat.Presheaf.Γgerm]
    simp only [Scheme.Opens.germ_stalkIso_hom_assoc,
      TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    simp only [Scheme.Opens.ι_appTop, TopCat.Presheaf.germ_res_assoc]
    change (((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫
      (Spec (.of (MvPowerSeries (Fin d) A))).presheaf.germ ⊤ (p.comap c.hom) trivial ≫
      (Spec.stalkIso (.of (MvPowerSeries (Fin d) A)) (p.comap c.hom)).hom).hom b) = _
    rw [Spec.germ_stalkMapIso_hom, Iso.inv_hom_id_assoc]
    rfl
  change j _ ∈ RingHom.ker l ^ n at hm
  rw [hmap] at hm
  have hzero := localized_low_coefficients A d p b n hm E hE
  have heq := RingHom.congr_fun
    (congrArg CommRingCat.Hom.hom (Spec.algebraMap_stalkIso_inv (R := .of A) p))
    (MvPowerSeries.coeff E b)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at heq
  rw [hzero, map_zero] at heq
  exact heq.symm

end AlgebraicGeometry.Scheme
