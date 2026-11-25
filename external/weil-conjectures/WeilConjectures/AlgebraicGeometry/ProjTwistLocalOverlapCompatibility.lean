/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.RingTheory.CoverModuleExact

import WeilConjectures.AlgebraicGeometry.ProjBasicOpenLocalizationDetection

/-!
# Finite localization data of twist sections

Source: Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- Detection after a further principal localization.
Source: Stacks Project, Tag 01M7, basic-open localization argument.
Write z=a/d with d a power of f. On D₊(f*g.num), f and g.num avoid the prime,
so g is a unit and a vanishes by the hypothesis. Basic-open localization detection
then gives (f*g.num)^N*a=0 for some N. In A_f, cancel the units coming from f,
d and g.den to obtain g^N*z=0. This is exactly zero in the module localization. -/
private theorem principal_localization_zero
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (g : HomogeneousLocalization.Away 𝒜 f) (z : LocalizedModule.Away f A)
    (hz : ∀ p : basicOpen 𝒜 f,
      let F := IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2)
      IsUnit (F (algebraMap (HomogeneousLocalization.Away 𝒜 f)
        (LocalizedModule.Away f A) g)) → F z = 0) :
    LocalizedModule.mkLinearMap (Submonoid.powers g) (LocalizedModule.Away f A) z = 0 := by
  classical
  let M := LocalizedModule.Away f A
  let q := algebraMap A M
  obtain ⟨⟨a, d⟩, hrep⟩ := IsLocalization.surj (Submonoid.powers f) z
  have ha : algebraMap A (LocalizedModule.Away (f * g.num) A) a = 0 := by
    apply basicOpen_localization_detection 𝒜 (f * g.num) (b + g.deg)
      (by omega) (SetLike.mul_mem_graded hf g.num_mem_deg) _ 0
    intro p
    have hfp : f ∉ p.1.asHomogeneousIdeal.toIdeal := fun h ↦
      p.2 (p.1.asHomogeneousIdeal.toIdeal.mul_mem_right g.num h)
    have hgp : g.num ∉ p.1.asHomogeneousIdeal.toIdeal := fun h ↦
      p.2 (p.1.asHomogeneousIdeal.toIdeal.mul_mem_left f h)
    let p' : basicOpen 𝒜 f := ⟨p.1, hfp⟩
    let F := IsLocalization.map (M := Submonoid.powers f) (S := M)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr hfp)
    have hden : q g.den * g.val = q g.num := by
      simpa only [Algebra.smul_def] using g.den_smul_val
    have hu : IsUnit (F g.val) := by
      have hnum : IsUnit (F (q g.num)) := by
        rw [IsLocalization.map_eq, RingHom.id_apply]
        exact IsLocalization.map_units
          (M := p.1.asHomogeneousIdeal.toIdeal.primeCompl) _ ⟨g.num, hgp⟩
      have heq := congrArg F hden
      rw [map_mul] at heq
      exact (IsUnit.mul_iff.mp (heq.symm ▸ hnum)).2
    have hz' : F z = 0 := hz p' hu
    have hap : algebraMap A (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) a = 0 := by
      have h := congrArg F hrep
      rw [map_mul, hz', zero_mul, IsLocalization.map_eq, RingHom.id_apply] at h
      exact h.symm
    rw [map_zero, IsLocalization.map_eq, RingHom.id_apply]
    exact hap
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (f * g.num)) (LocalizedModule.Away (f * g.num) A) a).mp ha
  obtain ⟨N, hN⟩ := u.prop
  change (f * g.num) ^ N = (u : A) at hN
  have hkill : q (f * g.num) ^ N * q a = 0 := by
    rw [← map_pow, ← map_mul, hN, hu, map_zero]
  have hn : q g.num ^ N * q a = 0 := by
    apply ((IsLocalization.Away.algebraMap_isUnit f (S := M)).pow N).mul_left_cancel
    simpa only [map_mul, mul_pow, mul_assoc, mul_zero] using hkill
  have hnz : q g.num ^ N * z = 0 := by
    apply (IsLocalization.map_units M d).mul_left_cancel
    calc
      q (d : A) * (q g.num ^ N * z) = q g.num ^ N * (z * q (d : A)) := by ring
      _ = 0 := by rw [hrep, hn]
      _ = q (d : A) * 0 := by rw [mul_zero]
  have hg : g.val ^ N * z = 0 := by
    apply ((IsLocalization.map_units M ⟨g.den, g.den_mem⟩).pow N).mul_left_cancel
    calc
      q g.den ^ N * (g.val ^ N * z) = q g.num ^ N * z := by
        rw [← mul_assoc, ← mul_pow]
        congr 1
        simpa only [Algebra.smul_def] using congrArg (fun x : M ↦ x ^ N) g.den_smul_val
      _ = 0 := hnz
      _ = q g.den ^ N * 0 := by rw [mul_zero]
  rw [← map_zero (LocalizedModule.mkLinearMap (Submonoid.powers g) M)]
  apply (IsLocalizedModule.eq_iff_exists (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)).mpr
  refine ⟨⟨g ^ N, ⟨N, rfl⟩⟩, ?_⟩
  change (g ^ N).val * z = (g ^ N).val * 0
  rw [mul_zero, HomogeneousLocalization.val_pow]
  exact hg

/-- Pointwise overlap equality for two fixed chart indices.
Source: Stacks Project, Tag 01M7, the local fraction comparison on a basic overlap.
(blueprint: lem-sc-proj-twist-local-overlap-pointwise)

Clear powers of the two chart denominators to write d*t_i=x/1 and e*t_j=y/1.
At each prime where g_i*g_j is invertible, scalar compatibility and the common
section value imply F(e*x-d*y)=0. Apply principal_localization_zero to this cross
numerator. The canonical lifts preserve x/1, y/1 and scalar multiplication;
therefore d*e times their difference is zero. Both d and e act invertibly on the
product localization, so their cancellation proves the asserted overlap equality. -/
theorem twist_localOverlap_pointwise
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f)))
    (n : ℕ) (g : Fin n → HomogeneousLocalization.Away 𝒜 f)
    (t : ∀ i : Fin n, LocalizedModule.Away (g i)
      (LocalizedModule.Away f A))
    (hlocal : ∀ (i : Fin n) (p : basicOpen 𝒜 f),
      let F := IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2)
      IsUnit (F (algebraMap (HomogeneousLocalization.Away 𝒜 f)
        (LocalizedModule.Away f A) (g i))) →
      ∃ e : LocalizedModule.Away (g i) (LocalizedModule.Away f A) →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal,
        (∀ z : LocalizedModule.Away f A,
          e (LocalizedModule.mkLinearMap (Submonoid.powers (g i))
            (LocalizedModule.Away f A) z) = F z) ∧
        (∀ (a : HomogeneousLocalization.Away 𝒜 f)
          (x : LocalizedModule.Away (g i) (LocalizedModule.Away f A)),
          e (a • x) = F (algebraMap (HomogeneousLocalization.Away 𝒜 f)
            (LocalizedModule.Away f A) a) * e x) ∧
        e (t i) = (s.1 p).1)
    (i j : Fin n) :
      let ρ := fun (a h : HomogeneousLocalization.Away 𝒜 f) (ha : a ∣ h) ↦
        IsLocalizedModule.lift (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a)
            (LocalizedModule.Away f A))
          (LocalizedModule.mkLinearMap (Submonoid.powers h)
            (LocalizedModule.Away f A))
          (RingTheory.localizationAway_map_units_of_dvd
            (M := LocalizedModule.Away f A) a h ha)
      ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
        ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j) := by
  classical
  dsimp only
  let B := HomogeneousLocalization.Away 𝒜 f
  let M := LocalizedModule.Away f A
  let loc (a : B) := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let ρ := fun (a h : B) (ha : a ∣ h) ↦
    IsLocalizedModule.lift (Submonoid.powers a) (loc a) (loc h)
      (RingTheory.localizationAway_map_units_of_dvd (M := M) a h ha)
  change ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
    ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j)
  obtain ⟨⟨x, d⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers (g i)) (loc (g i)) (t i)
  obtain ⟨⟨y, e⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers (g j)) (loc (g j)) (t j)
  change (d : B) • t i = loc (g i) x at hx
  change (e : B) • t j = loc (g j) y at hy
  have hzero : loc (g i * g j) ((e : B) • x - (d : B) • y) = 0 := by
    apply principal_localization_zero 𝒜 f b hb hf
    intro p
    dsimp only
    intro hu
    let F := IsLocalization.map (M := Submonoid.powers f) (S := M)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2)
    have hui : IsUnit (F (algebraMap B M (g i))) := by
      have hu' : IsUnit (F (algebraMap B M (g i)) * F (algebraMap B M (g j))) := by
        simpa only [map_mul] using hu
      exact (IsUnit.mul_iff.mp hu').1
    have huj : IsUnit (F (algebraMap B M (g j))) := by
      have hu' : IsUnit (F (algebraMap B M (g i)) * F (algebraMap B M (g j))) := by
        simpa only [map_mul] using hu
      exact (IsUnit.mul_iff.mp hu').2
    obtain ⟨ei, hei, hsi, hti⟩ := hlocal i p hui
    obtain ⟨ej, hej, hsj, htj⟩ := hlocal j p huj
    have hFx : F x = F (algebraMap B M (d : B)) * (s.1 p).1 := by
      rw [← hei x, ← hx, hsi, hti]
    have hFy : F y = F (algebraMap B M (e : B)) * (s.1 p).1 := by
      rw [← hej y, ← hy, hsj, htj]
    change F ((e : B) • x - (d : B) • y) = 0
    simp only [map_sub, Algebra.smul_def, map_mul, hFx, hFy]
    ring
  have hcross : (e : B) • loc (g i * g j) x =
      (d : B) • loc (g i * g j) y := by
    apply sub_eq_zero.mp
    simpa only [loc, map_sub, map_smul] using hzero
  have hlocx : loc (g i * g j) x =
      (d : B) • ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) := by
    rw [← IsLocalizedModule.lift_apply (Submonoid.powers (g i)) (loc (g i))
      (loc (g i * g j))
      (RingTheory.localizationAway_map_units_of_dvd (M := M) _ _
        (dvd_mul_right (g i) (g j))) x, ← hx, map_smul]
  have hlocy : loc (g i * g j) y =
      (e : B) • ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j) := by
    rw [← IsLocalizedModule.lift_apply (Submonoid.powers (g j)) (loc (g j))
      (loc (g i * g j))
      (RingTheory.localizationAway_map_units_of_dvd (M := M) _ _
        (dvd_mul_left (g j) (g i))) y, ← hy, map_smul]
  rw [hlocx, hlocy, smul_comm (e : B) (d : B)] at hcross
  have hd := RingTheory.localizationAway_map_units_of_dvd (M := M)
    (g i) (g i * g j) (dvd_mul_right (g i) (g j)) d
  have he := RingTheory.localizationAway_map_units_of_dvd (M := M)
    (g j) (g i * g j) (dvd_mul_left (g j) (g i)) e
  exact ((Module.End.isUnit_iff _).mp he).1 (((Module.End.isUnit_iff _).mp hd).1 hcross)

/-- Local fractions `t i` over the principal opens `D(g i)` of the chart of `D₊(f)` that
evaluate to a twist section `s` at every point agree on each overlap `D(g i * g j)`.
(blueprint: lem-sc-proj-twist-local-overlap-compatibility) -/
theorem twist_localOverlap_compatibility
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∀ (n : ℕ) (g : Fin n → B) (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      (∀ (i : Fin n) (p : basicOpen 𝒜 f),
      let F := IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2)
      IsUnit (F (algebraMap B (Localization.Away f) (g i))) →
      ∃ e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal,
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) = F z) ∧
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) = F (algebraMap B (Localization.Away f) a) * e x) ∧
        e (t i) = (s.1 p).1) →
      let ρ := fun (a h : B) (ha : a ∣ h) ↦
        IsLocalizedModule.lift (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
          (RingTheory.localizationAway_map_units_of_dvd (M := M) a h ha)
      ∀ i j : Fin n,
        ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
          ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j) := by
  dsimp
  intro n g t hlocal i j
  exact twist_localOverlap_pointwise 𝒜 k f b hb hf s n g t hlocal i j

end AlgebraicGeometry.Proj
