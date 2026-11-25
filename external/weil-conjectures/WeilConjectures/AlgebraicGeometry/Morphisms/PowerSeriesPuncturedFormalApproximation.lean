/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFiniteOrderApprox
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedIdealDetection

/-!
# Formal approximation of sections along the punctured zero section

## References

* Stacks Project, Tag 0EY9, the first displayed inverse-limit calculation
* Stacks Project, Tag 0EY9, first displayed calculation and the following comparison of rings
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Global variable-ideal powers map to powers of the zero-section stalk kernels.
This follows from naturality of `ΓSpecIso`, open restriction, and germs. -/
private lemma powerSeries_variables_pow_germs
    (A : Type u) [CommRing A] (d : ℕ)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens) :
    let z := Spec.map
      (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
    let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
    ∀ (b : MvPowerSeries (Fin d) A) (n : ℕ),
      b ∈ (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin d) (R := A)))) ^ n →
        ∀ x : (z ⁻¹ᵁ V).toScheme,
          (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom (r b) ∈
            (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n := by
  dsimp only
  let z := Spec.map
    (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
  let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
  let I : Ideal (MvPowerSeries (Fin d) A) := Ideal.span (Set.range MvPowerSeries.X)
  have hres : V.ι.appTop ≫ (z ∣_ V).appTop =
      z.appTop ≫ (z ⁻¹ᵁ V).ι.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg Scheme.Hom.appTop (morphismRestrict_ι z V)
  have hcc : (ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫
      V.ι.appTop ≫ (z ∣_ V).appTop =
      CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) ≫
        (ΓSpecIso (.of A)).inv ≫ (z ⁻¹ᵁ V).ι.appTop := by
    rw [hres, ← Category.assoc, ← ΓSpecIso_inv_naturality, Category.assoc]
  intro b n hb x
  let g := (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom.comp r
  let J := RingHom.ker ((z ∣_ V).stalkMap x).hom
  have hI : I ≤ J.comap g := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ((z ∣_ V).stalkMap x).hom
      ((V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom (r (MvPowerSeries.X i))) = 0
    have hzero : ((z ∣_ V).appTop).hom (r (MvPowerSeries.X i)) = 0 := by
      have heq := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hcc)
        (MvPowerSeries.X i)
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
        MvPowerSeries.constantCoeff_X, map_zero, r, CommRingCat.hom_comp,
        RingHom.comp_apply] using heq
    rw [TopCat.Presheaf.Γgerm, Scheme.Hom.germ_stalkMap_apply]
    have hzero' : (z ∣_ V).app ⊤ (r (MvPowerSeries.X i)) = 0 := by
      exact hzero
    rw [hzero', map_zero]
  exact (le_trans (pow_le_pow_left' hI n) (Ideal.le_comap_pow g n)) hb

/-- Every section has a unique power series with the same restrictions to all
infinitesimal neighbourhoods of the punctured zero section. -/
theorem existsUnique_powerSeries_punctured_formal_approximation
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    let z := Spec.map
      (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
    let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
    ∀ s : Γ(V.toScheme, ⊤), ∃! b : MvPowerSeries (Fin d) A,
      ∀ (x : (z ⁻¹ᵁ V).toScheme) (n : ℕ),
        (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom (s - r b) ∈
          (RingHom.ker ((z ∣_ V).stalkMap x).hom) ^ n := by
  classical
  dsimp only
  intro s
  let z := Spec.map
    (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
  let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
  let I : Ideal (MvPowerSeries (Fin d) A) := Ideal.span (Set.range MvPowerSeries.X)
  let g (x : (z ⁻¹ᵁ V).toScheme) :=
    (V.toScheme.presheaf.Γgerm ((z ∣_ V) x)).hom
  let J (x : (z ⁻¹ᵁ V).toScheme) := RingHom.ker ((z ∣_ V).stalkMap x).hom
  have htest (b : MvPowerSeries (Fin d) A) (n : ℕ) :
      b ∈ I ^ n ↔ ∀ x, g x (r b) ∈ J x ^ n :=
    ⟨powerSeries_variables_pow_germs A d V b n,
      powerSeries_mem_variables_pow_of_punctured_germs A hdepth d hd V hV b n⟩
  have hfinite (n : ℕ) : ∃ b : MvPowerSeries (Fin d) A,
      ∀ x, g x (s - r b) ∈ J x ^ n :=
    exists_powerSeries_punctured_finite_order_approximation A hdepth d hd V hV s n
  choose f hf using hfinite
  have hcauchy {m n : ℕ} (hmn : m ≤ n) : f m - f n ∈ I ^ m := by
    apply (htest _ _).mpr
    intro x
    have hm := hf m x
    have hn := Ideal.pow_le_pow_right hmn (hf n x)
    have heq : g x (r (f m - f n)) =
        g x (s - r (f n)) - g x (s - r (f m)) := by
      simp only [map_sub]
      abel
    rw [heq]
    exact (J x ^ m).sub_mem hn hm
  have hcauchy' : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule (MvPowerSeries (Fin d) A)
        (MvPowerSeries (Fin d) A))] := by
    intro m n hmn
    simpa only [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using hcauchy hmn
  obtain ⟨b, hb⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I
    (MvPowerSeries (Fin d) A)) hcauchy'
  have hbmem (n : ℕ) : f n - b ∈ I ^ n := by
    simpa only [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using hb n
  have happ : ∀ x n, g x (s - r b) ∈ J x ^ n := by
    intro x n
    have hdiff := (htest _ n).mp (hbmem n) x
    have heq : g x (s - r b) = g x (s - r (f n)) + g x (r (f n - b)) := by
      simp only [map_sub]
      abel
    rw [heq]
    exact (J x ^ n).add_mem (hf n x) hdiff
  refine ⟨b, happ, ?_⟩
  intro c hc
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  have hmem : c - b ∈ I ^ n := by
    apply (htest _ n).mpr
    intro x
    have heq : g x (r (c - b)) = g x (s - r b) - g x (s - r c) := by
      simp only [map_sub]
      abel
    rw [heq]
    exact (J x ^ n).sub_mem (happ x n) (hc x n)
  simpa only [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using hmem

end AlgebraicGeometry.Scheme
