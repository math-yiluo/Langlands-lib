/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Localization.Ideal

/-! # Stalk kernels of finite power-series thickenings

## References

* Stacks Project, Tag 0EY9, the first displayed calculation
* Stacks Project, Tag 0EY9, the finite-index structure-sheaf comparison
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private lemma quotient_local_kernel {R : Type*} [CommRing R] (I : Ideal R)
    (p : PrimeSpectrum (R ⧸ I)) :
    RingHom.ker (Localization.localRingHom
      (p.comap (Ideal.Quotient.mk I)).asIdeal p.asIdeal (Ideal.Quotient.mk I) rfl) =
      I.map (algebraMap R (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)).asIdeal)) := by
  ext a
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (p.comap (Ideal.Quotient.mk I)).asIdeal.primeCompl a
  rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (t : R ⧸ I)
    refine ⟨b, ?_, ?_⟩
    · change (Ideal.Quotient.mk I) b ∉ p.asIdeal
      rw [hb]
      exact t.2
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, hb] using ht
  · rintro ⟨b, hb, hbr⟩
    refine ⟨⟨(Ideal.Quotient.mk I) b, hb⟩, ?_⟩
    simpa only [← map_mul] using Ideal.Quotient.eq_zero_iff_mem.mpr hbr

set_option backward.isDefEq.respectTransparency false in
private lemma quotient_germ_mem_image (R : Type*) [CommRing R] (I : Ideal R)
    (V : (Spec (.of R)).Opens) (s : Γ(V.toScheme, ⊤)) :
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    ((q ∣_ V).appTop).hom s = 0 →
    ∀ y : (q ⁻¹ᵁ V).toScheme,
      (V.toScheme.presheaf.Γgerm ((q ∣_ V) y)).hom s ∈
        I.map (((ΓSpecIso (.of R)).inv ≫ V.ι.appTop ≫
          V.toScheme.presheaf.Γgerm ((q ∣_ V) y)).hom) := by
  dsimp only
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  intro hs y
  let a := (V.toScheme.presheaf.Γgerm ((q ∣_ V) y)).hom s
  let e := morphismRestrictStalkMap q V y ≪≫
    Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) y.1
  have hz : ((q ∣_ V).stalkMap y).hom a = 0 := by
    dsimp [a]
    rw [TopCat.Presheaf.Γgerm, Scheme.Hom.germ_stalkMap_apply]
    change ((q ⁻¹ᵁ V).toScheme.presheaf.germ _ y _).hom
      (((q ∣_ V).appTop).hom s) = 0
    rw [hs, map_zero]
  have hloc : e.hom.left a ∈ RingHom.ker
      (Localization.localRingHom (y.1.comap (Ideal.Quotient.mk I)).asIdeal
        y.1.asIdeal (Ideal.Quotient.mk I) rfl) := by
    change (Localization.localRingHom _ _ _ rfl) (e.hom.left a) = 0
    have hh := RingHom.congr_fun (congrArg CommRingCat.Hom.hom e.hom.w) a
    change (Localization.localRingHom _ _ _ rfl) (e.hom.left a) =
      e.hom.right (((q ∣_ V).stalkMap y).hom a) at hh
    rw [hz, map_zero] at hh
    exact hh
  rw [quotient_local_kernel] at hloc
  have hmap : CommRingCat.ofHom (algebraMap R
      (Localization.AtPrime (y.1.comap (Ideal.Quotient.mk I)).asIdeal)) ≫ e.inv.left =
      (ΓSpecIso (.of R)).inv ≫ V.ι.appTop ≫
        V.toScheme.presheaf.Γgerm ((q ∣_ V) y) := by
    simp only [e, Iso.trans_inv, Arrow.comp_left, Scheme.arrowStalkMapSpecIso,
      morphismRestrictStalkMap, Arrow.isoMk', Arrow.isoMk_inv_left, Iso.trans_inv,
      TopCat.Presheaf.Γgerm, Scheme.Opens.stalkIso_inv]
    erw [Spec.algebraMap_stalkIso_inv_assoc]
    simp only [TopCat.Presheaf.stalkCongr_inv]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
    erw [Scheme.Hom.germ_stalkMap]
    rfl
  have hm := Ideal.mem_map_of_mem e.inv.left.hom hloc
  rw [Ideal.map_map] at hm
  change e.inv.left.hom (e.hom.left.hom a) ∈
    I.map ((CommRingCat.ofHom (algebraMap R _) ≫ e.inv.left).hom) at hm
  erw [hmap] at hm
  have hid := RingHom.congr_fun
    (congrArg CommRingCat.Hom.hom (Arrow.hom_inv_id_left e)) a
  change e.inv.left.hom (e.hom.left.hom a) = a at hid
  rw [hid] at hm
  exact hm


set_option backward.isDefEq.respectTransparency false in
/-- A section vanishing on the finite thickening has germs in the corresponding
powers of the zero-section stalk kernels.
-/
theorem powerSeries_punctured_germs_mem_pow_of_thickening_zero
    (A : Type u) [CommRing A] (d : ℕ)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens) (n : ℕ) :
    let I : Ideal (MvPowerSeries (Fin d) A) := Ideal.span (Set.range MvPowerSeries.X)
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))
    let z := Spec.map
      (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
    ∀ t : Γ(V.toScheme, ⊤), ((q ∣_ V).appTop).hom t = 0 →
      ∀ x : (z ⁻¹ᵁ V).toScheme,
        (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom t ∈
          (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n  := by
  classical
  dsimp only
  let B := MvPowerSeries (Fin d) A
  let I : Ideal B := Ideal.span (Set.range MvPowerSeries.X)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))
  let z := Spec.map
    (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
  intro t ht x
  by_cases hn : n = 0
  · subst n
    simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  have hI : I ≤ (PrimeSpectrum.comap
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) x.1).asIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPowerSeries.constantCoeff (MvPowerSeries.X i) ∈ x.1.asIdeal
    simp only [MvPowerSeries.constantCoeff_X, Ideal.zero_mem]
  have hIn : I ^ n ≤ (PrimeSpectrum.comap
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) x.1).asIdeal :=
    (Ideal.pow_le_self hn).trans hI
  obtain ⟨y, hy⟩ : PrimeSpectrum.comap
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) x.1 ∈
        Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n))) := by
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
    exact hIn
  have hyp : q y = z x.1 := hy
  let yV : (q ⁻¹ᵁ V).toScheme := ⟨y, by
    change q y ∈ V
    rw [hyp]
    exact x.2⟩
  have hv : (q ∣_ V) yV = (z ∣_ V) x := by
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe] using hyp
  have hm := quotient_germ_mem_image B (I ^ n) V t ht yV
  rw [hv] at hm
  let g := ((ΓSpecIso (.of B)).inv ≫ V.ι.appTop ≫
    V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom
  let J := RingHom.ker ((z ∣_ V).stalkMap x).hom
  have hres : V.ι.appTop ≫ (z ∣_ V).appTop =
      z.appTop ≫ (z ⁻¹ᵁ V).ι.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg Scheme.Hom.appTop (morphismRestrict_ι z V)
  have hcc : (ΓSpecIso (.of B)).inv ≫ V.ι.appTop ≫ (z ∣_ V).appTop =
      CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) ≫
        (ΓSpecIso (.of A)).inv ≫ (z ⁻¹ᵁ V).ι.appTop := by
    rw [hres, ← Category.assoc, ← ΓSpecIso_inv_naturality, Category.assoc]
  have hIJ : I ≤ J.comap g := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ((z ∣_ V).stalkMap x).hom
      ((V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom
        (((ΓSpecIso (.of B)).inv ≫ V.ι.appTop).hom (MvPowerSeries.X i))) = 0
    have hzero : ((z ∣_ V).appTop).hom
        (((ΓSpecIso (.of B)).inv ≫ V.ι.appTop).hom (MvPowerSeries.X i)) = 0 := by
      have heq := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hcc)
        (MvPowerSeries.X i)
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
        B, MvPowerSeries.constantCoeff_X, map_zero] using heq
    rw [TopCat.Presheaf.Γgerm, Scheme.Hom.germ_stalkMap_apply]
    change ((z ⁻¹ᵁ V).toScheme.presheaf.germ _ x _).hom
      (((z ∣_ V).appTop).hom
        (((ΓSpecIso (.of B)).inv ≫ V.ι.appTop).hom (MvPowerSeries.X i))) = 0
    rw [hzero, map_zero]
  have hmap : I.map g ≤ J := Ideal.map_le_iff_le_comap.mpr hIJ
  have hm' : (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom t ∈ (I ^ n).map g := hm
  rw [Ideal.map_pow] at hm'
  exact (pow_le_pow_left' hmap n) hm'


end AlgebraicGeometry.Scheme
