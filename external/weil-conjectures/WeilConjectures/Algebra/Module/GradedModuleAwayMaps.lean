/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# GradedModuleAwayMaps

Source: Stacks Project, Constructions, Lemma 01M4.
-/

@[expose] public section

universe u v

namespace LocalizedModule

set_option backward.isDefEq.respectTransparency false

private theorem zeroFractionsSubmodule
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
    (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (x : M),
      a ∈ 𝒜 n → x ∈ 𝓜 z → a • x ∈ 𝓜 (n + z)) (f : S) :
    let := Module.compHom (LocalizedModule.Away f M)
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
    ∃ Z : Submodule (HomogeneousLocalization.Away 𝒜 f) (LocalizedModule.Away f M),
      (Z : Set (LocalizedModule.Away f M)) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f) := by
  let := Module.compHom (LocalizedModule.Away f M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  refine ⟨{ carrier := degreeZeroFractions
              (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
              (Submonoid.powers f)
            zero_mem' := ?_
            add_mem' := ?_
            smul_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨i, x, s, hx, hs, rfl⟩ ⟨j, y, t, hy, ht, rfl⟩
    refine ⟨i + j, (t : S) • x + (s : S) • y, s * t, ?_,
      SetLike.mul_mem_graded hs ht, mk_add_mk.symm⟩
    apply (𝓜 ((i + j : ℕ) : ℤ)).add_mem
    · simpa [Nat.cast_add, add_comm] using hsmul j i t x ht hx
    · simpa [Nat.cast_add] using hsmul i j s y hs hy
  · exact ⟨0, 0, 1, (𝓜 0).zero_mem, SetLike.GradedOne.one_mem, zero_mk 1⟩
  · rintro r _ ⟨i, x, s, hx, hs, rfl⟩
    obtain ⟨q, rfl⟩ := HomogeneousLocalization.mk_surjective r
    refine ⟨q.deg + i, (q.num : S) • x, ⟨q.den, q.den_mem⟩ * s, ?_,
      SetLike.mul_mem_graded q.den.2 hs, ?_⟩
    · simpa [Nat.cast_add] using hsmul q.deg i q.num x q.num.2 hx
    · change mk _ _ = HomogeneousLocalization.val (HomogeneousLocalization.mk q) • mk x s
      exact (mk_smul_mk _ _ _ _).symm

private theorem relationInverse
    {S : Type u} [CommRing S] (f g a : S) (e : ℕ) (h : g ^ e = a * f) :
    algebraMap S (Localization.Away g) f *
      Localization.mk a (⟨g ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers g) = 1 := by
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul]
  change Localization.mk (f * a) (⟨g ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers g) = 1
  rw [mul_comm f a, ← h, Localization.mk_eq_mk']
  exact IsLocalization.mk'_self' (Localization.Away g)


private theorem ordinaryAwayMaps
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
    (f g : S) (p : ∃ (e : ℕ) (a : S), g ^ e = a * f) :
    ∃ (l : LocalizedModule.Away f M →ₗ[S] LocalizedModule.Away g M)
      (lS : Localization.Away f →+* Localization.Away g),
      IsUnit (algebraMap S (Localization.Away g) f) ∧
      Function.Bijective (fun x : LocalizedModule.Away g M ↦ f • x) ∧
      (∀ (e : ℕ) (a : S), g ^ e = a * f →
        algebraMap S (Localization.Away g) f * Localization.mk a
          (⟨g ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers g) = 1) ∧
      (∀ x : M, l (mk x 1) = mk x 1) ∧
      (∀ T : LocalizedModule.Away f M →ₗ[S] LocalizedModule.Away g M,
        (∀ x : M, T (mk x 1) = mk x 1) → T = l) ∧
      (∀ (e : ℕ) (a : S), g ^ e = a * f → ∀ (x : M) (m : ℕ),
        l (mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) =
          mk (a ^ m • x) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) ∧
      (∀ r : S, lS (algebraMap S (Localization.Away f) r) =
        algebraMap S (Localization.Away g) r) ∧
      (∀ (r : Localization.Away f) (x : LocalizedModule.Away f M),
        l (r • x) = lS r • l x) := by
  obtain ⟨e, a, ha⟩ := p
  have hu : IsUnit (algebraMap S (Localization.Away g) f) :=
    isUnit_iff_exists_inv.mpr ⟨_, relationInverse f g a e ha⟩
  have hb : Function.Bijective (fun x : LocalizedModule.Away g M ↦ f • x) := by
    simpa only [algebraMap_smul] using hu.smul_bijective (β := LocalizedModule.Away g M)
  have units : ∀ s : Submonoid.powers f,
      IsUnit (algebraMap S (Module.End S (LocalizedModule.Away g M)) s) := by
    rintro ⟨_, m, rfl⟩
    rw [map_pow]
    exact ((Module.End.isUnit_iff _).mpr hb).pow m
  let l := lift (Submonoid.powers f) (mkLinearMap (Submonoid.powers g) M) units
  let lS := Localization.awayLift (algebraMap S (Localization.Away g)) f hu
  have hl : ∀ x : M, l (mk x 1) = mk x 1 := by
    intro x
    exact lift_mk_one (Submonoid.powers f)
      (mkLinearMap (Submonoid.powers g) M) units x
  have hls : ∀ r : S, lS (algebraMap S (Localization.Away f) r) =
      algebraMap S (Localization.Away g) r := IsLocalization.Away.lift_eq f hu
  refine ⟨l, lS, hu, hb, fun e a h ↦ relationInverse f g a e h, hl, ?_, ?_, hls, ?_⟩
  · intro T hT
    symm
    apply lift_unique
    ext x
    exact hT x
  · intro e a h x m
    have hm : Function.Injective (fun y : LocalizedModule.Away g M ↦ f ^ m • y) := by
      simpa only [algebraMap_smul, ← map_pow] using
        (hu.pow m).smul_bijective (β := LocalizedModule.Away g M) |>.injective
    apply hm
    dsimp only
    have hc : f ^ m • mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) =
        mk x (1 : Submonoid.powers f) := by
      rw [smul'_mk]
      exact mk_cancel (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) x
    rw [← l.map_smul, hc, hl, smul'_mk]
    have heq : f ^ m • (a ^ m • x) = g ^ (e * m) • x := by
      rw [← mul_smul, ← mul_pow, mul_comm f a, ← h, ← pow_mul]
    rw [heq]
    exact (mk_cancel (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g) x).symm
  · intro r x
    induction r using Localization.induction_on with
    | H q =>
      obtain ⟨b, s⟩ := q
      have hs : IsUnit (algebraMap S (Localization.Away g) (s : S)) := by
        obtain ⟨_, m, rfl⟩ := s
        simpa only [map_pow] using hu.pow m
      have hr : algebraMap S (Localization.Away f) (s : S) * Localization.mk b s =
          algebraMap S (Localization.Away f) b := by
        rw [Localization.mk_eq_mk']
        exact IsLocalization.mk'_spec' (Localization.Away f) _ _
      have hr' : algebraMap S (Localization.Away g) (s : S) * lS (Localization.mk b s) =
          algebraMap S (Localization.Away g) b := by
        rw [← hls, ← map_mul, hr, hls]
      apply hs.smul_bijective.injective
      calc
        algebraMap S (Localization.Away g) (s : S) • l (Localization.mk b s • x) =
            l (algebraMap S (Localization.Away f) (s : S) •
              (Localization.mk b s • x)) := by
          simp only [algebraMap_smul, l.map_smul]
        _ = b • l x := by rw [← mul_smul, hr, algebraMap_smul, l.map_smul]
        _ = algebraMap S (Localization.Away g) (s : S) •
            (lS (Localization.mk b s) • l x) := by
          rw [← mul_smul, hr', algebraMap_smul]

private theorem degreeZeroImage
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
    (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (x : M),
      a ∈ 𝒜 n → x ∈ 𝓜 z → a • x ∈ 𝓜 (n + z))
    (f g : S) (d δ : ℕ) (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 δ)
    (e k : ℕ) (a : S) (ha : a ∈ 𝒜 k) (h : g ^ e = a * f)
    (l : LocalizedModule.Away f M →ₗ[S] LocalizedModule.Away g M)
    (hl : ∀ (x : M) (m : ℕ),
      l (mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) =
        mk (a ^ m • x) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) :
    ∀ x ∈ degreeZeroFractions (fun n : ℕ ↦ (𝒜 n : Set S))
      (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f),
      l x ∈ degreeZeroFractions (fun n : ℕ ↦ (𝒜 n : Set S))
        (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers g) := by
  rintro _ ⟨i, x, s, hx, hs, rfl⟩
  obtain ⟨s, m, rfl⟩ := s
  by_cases hn : ∃ n : ℕ, g ^ n = 0
  · obtain ⟨n, hn⟩ := hn
    have := LocalizedModule.subsingleton (M := M) (S := Submonoid.powers g) ⟨n, hn⟩
    exact ⟨0, 0, 1, (𝓜 0).zero_mem, SetLike.GradedOne.one_mem,
      Subsingleton.elim _ _⟩
  have hgn : ∀ n : ℕ, g ^ n ≠ 0 := by simpa only [not_exists] using hn
  have hfm : f ^ m ≠ 0 := by
    intro hfm
    apply hgn (e * m)
    rw [pow_mul, h, mul_pow, hfm, mul_zero]
  have hi : i = m * d := by
    exact DirectSum.degree_eq_of_mem_mem 𝒜 hs
      (by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded m hf) hfm
  have hk : k + d = e * δ := by
    apply DirectSum.degree_eq_of_mem_mem 𝒜 (SetLike.mul_mem_graded ha hf)
      (by simpa [h, nsmul_eq_mul] using SetLike.pow_mem_graded e hg)
    rw [← h]
    exact hgn e
  refine ⟨e * m * δ, a ^ m • x,
    ⟨g ^ (e * m), ⟨e * m, rfl⟩⟩, ?_, ?_, (hl x m).symm⟩
  · have H := hsmul (m * k) i (a ^ m) x
      (by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded m ha) hx
    have hd : m * k + i = e * m * δ := by rw [hi]; nlinarith [hk]
    change a ^ m • x ∈ 𝓜 ((e * m * δ : ℕ) : ℤ)
    simpa only [← Nat.cast_add, hd] using H
  · simpa [nsmul_eq_mul] using SetLike.pow_mem_graded (e * m) hg

private theorem ringFractionFormula
    {S : Type u} [CommRing S] (f g : S)
    (lS : Localization.Away f →+* Localization.Away g)
    (hlS : ∀ r : S, lS (algebraMap S (Localization.Away f) r) =
      algebraMap S (Localization.Away g) r)
    (e : ℕ) (a : S) (h : g ^ e = a * f) (b : S) (m : ℕ) :
    lS (Localization.mk b (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) =
      Localization.mk (a ^ m * b)
        (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g) := by
  have hi := relationInverse f g a e h
  have heq : lS = Localization.awayLift (algebraMap S (Localization.Away g)) f
      (isUnit_iff_exists_inv.mpr ⟨_, hi⟩) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    rw [RingHom.comp_apply, RingHom.comp_apply, hlS, IsLocalization.Away.lift_eq]
  rw [heq, Localization.awayLift_mk _ _ _ _ hi]
  rw [Localization.mk_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul]
  congr 1
  · exact mul_comm _ _
  · apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    exact (pow_mul _ _ _).symm

private theorem homogeneousRingImage
    {S : Type u} [CommRing S]
    (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (f g : S) (d δ : ℕ) (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 δ)
    (e k : ℕ) (a : S) (ha : a ∈ 𝒜 k) (h : g ^ e = a * f)
    (lS : Localization.Away f →+* Localization.Away g)
    (hlS : ∀ r : S, lS (algebraMap S (Localization.Away f) r) =
      algebraMap S (Localization.Away g) r) :
    ∀ r : HomogeneousLocalization.Away 𝒜 f,
      ∃ t : HomogeneousLocalization.Away 𝒜 g, t.val = lS r.val := by
  intro r
  obtain ⟨q, rfl⟩ := HomogeneousLocalization.mk_surjective r
  rcases q with ⟨i, ⟨b, hb⟩, ⟨s, hs⟩, hsP⟩
  obtain ⟨m, hm⟩ := hsP
  change f ^ m = s at hm
  subst s
  by_cases hn : ∃ n : ℕ, g ^ n = 0
  · obtain ⟨n, hn⟩ := hn
    have := IsLocalization.subsingleton (M := Submonoid.powers g)
      (S := Localization.Away g) ⟨n, hn⟩
    exact ⟨0, Subsingleton.elim _ _⟩
  have hgn : ∀ n : ℕ, g ^ n ≠ 0 := by simpa only [not_exists] using hn
  have hfm : f ^ m ≠ 0 := by
    intro hfm
    apply hgn (e * m)
    rw [pow_mul, h, mul_pow, hfm, mul_zero]
  have hi : i = m * d := DirectSum.degree_eq_of_mem_mem 𝒜 hs
    (by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded m hf) hfm
  have hk : k + d = e * δ := by
    apply DirectSum.degree_eq_of_mem_mem 𝒜 (SetLike.mul_mem_graded ha hf)
      (by simpa [h, nsmul_eq_mul] using SetLike.pow_mem_graded e hg)
    rw [← h]
    exact hgn e
  refine ⟨HomogeneousLocalization.mk ⟨e * m * δ, ⟨a ^ m * b, ?_⟩,
    ⟨g ^ (e * m), ?_⟩, ⟨e * m, rfl⟩⟩, ?_⟩
  · have hd : m * k + i = e * m * δ := by rw [hi]; nlinarith [hk]
    rw [← hd]
    exact SetLike.mul_mem_graded
      (by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded m ha) hb
  · simpa [nsmul_eq_mul] using SetLike.pow_mem_graded (e * m) hg
  · exact (ringFractionFormula f g lS hlS e a h b m).symm

set_option linter.unusedVariables false in
/-- Construction of the ordinary and degree-zero restriction maps, before imposing coherence.
Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open), proof of
(1)(a),(c),(d),(g).
(blueprint: lem-weil-pbc-graded-module-away-maps)

Proof: Equal-degree fractions form a submodule: put sums over a common denominator,
and multiply homogeneous numerators and denominators to check scalar closure. If g is
nilpotent the target localization is zero. Otherwise g^e = af is nonzero, so directness
of the ring grading forces deg a + deg f = e * deg g. The image of f in S_g is a unit
with inverse a/g^e. The module localization universal property therefore produces the
unique lambda extending x/1, with formula x/f^m mapped to a^m*x/g^(e*m). The ring
universal property produces lambdaS; checking on fractions gives semilinearity. The
degree equation shows these maps preserve equal-degree fractions; restrict them to rho
and rhoS. Define U by g^(deg f)/f^(deg g), whose numerator and denominator have equal
degree. In the target its inverse is f^(deg g)/g^(deg f), again of degree zero.
Multiplying these fractions proves that rhoS(U) is a unit, including the zero-ring case. -/
theorem gradedModuleAwayMaps
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
    (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (x : M),
      a ∈ 𝒜 n → x ∈ 𝓜 z → a • x ∈ 𝓜 (n + z)) :
    let F := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
    let R := fun f : F ↦ HomogeneousLocalization.Away 𝒜 f.val.1
    let L := fun f : F ↦ Localization.Away f.val.1
    let N := fun f : F ↦ LocalizedModule.Away f.val.1 M
    let Rel := fun f g : F ↦ ∃ (e k : ℕ) (a : S),
      0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1
    letI : ∀ f : F, Module (R f) (N f) :=
      fun f ↦ Module.compHom (N f) (algebraMap (R f) (L f))
    ∃ (Z : ∀ f : F, Submodule (R f) (N f)),
      (∀ f : F, (Z f : Set (N f)) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)) ∧
    ∃ (lambda : ∀ (f g : F), Rel f g → N f →ₗ[S] N g)
      (lambdaS : ∀ (f g : F), Rel f g → L f →+* L g)
      (rho : ∀ (f g : F), Rel f g → Z f →+ Z g)
      (rhoS : ∀ (f g : F), Rel f g → R f →+* R g)
      (U : ∀ (f g : F), R f),
      (∀ (f g : F), (U f g).val = Localization.mk (g.val.1 ^ f.val.2)
        (⟨f.val.1 ^ g.val.2, ⟨g.val.2, rfl⟩⟩ : Submonoid.powers f.val.1)) ∧
      (∀ (f g : F) (p : Rel f g),
        IsUnit (algebraMap S (L g) f.val.1) ∧
        Function.Bijective (fun x : N g ↦ f.val.1 • x) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k →
          g.val.1 ^ e = a * f.val.1 →
          algebraMap S (L g) f.val.1 * Localization.mk a
            (⟨g.val.1 ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers g.val.1) = 1) ∧
        (∀ x : M, lambda f g p (mk x 1) = mk x 1) ∧
        (∀ T : N f →ₗ[S] N g,
          (∀ x : M, T (mk x 1) = mk x 1) → T = lambda f g p) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k →
          g.val.1 ^ e = a * f.val.1 → ∀ (x : M) (m : ℕ),
          lambda f g p (mk x (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1)) =
            mk (a ^ m • x)
              (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1)) ∧
        (∀ r : S, lambdaS f g p (algebraMap S (L f) r) = algebraMap S (L g) r) ∧
        (∀ (r : L f) (x : N f),
          lambda f g p (r • x) = lambdaS f g p r • lambda f g p x) ∧
        (∀ x : Z f, (rho f g p x : N g) = lambda f g p (x : N f)) ∧
        (∀ r : R f, (rhoS f g p r).val = lambdaS f g p r.val) ∧
        (∀ (r : R f) (x : Z f), rho f g p (r • x) = rhoS f g p r • rho f g p x) ∧
        IsUnit (rhoS f g p (U f g))) := by
  classical
  dsimp only
  let F := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
  let R := fun f : F ↦ HomogeneousLocalization.Away 𝒜 f.val.1
  let L := fun f : F ↦ Localization.Away f.val.1
  let N := fun f : F ↦ LocalizedModule.Away f.val.1 M
  let Rel := fun f g : F ↦ ∃ (e k : ℕ) (a : S),
      0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1
  let : ∀ f : F, Module (R f) (N f) :=
      fun f ↦ Module.compHom (N f) (algebraMap (R f) (L f))
  change ∃ (Z : ∀ f : F, Submodule (R f) (N f)), _
  have hz (f : F) := zeroFractionsSubmodule 𝒜 𝓜 hsmul f.val.1
  choose Z hZ using hz
  have hm (f g : F) (p : Rel f g) := ordinaryAwayMaps (M := M) f.val.1 g.val.1
    (by obtain ⟨e, k, a, he, ha, h⟩ := p; exact ⟨e, a, h⟩)
  choose lambda lambdaS hunit hbij hinv hnum huniq hformula hring hsemi using hm
  have hpres (f g : F) (p : Rel f g) (x : Z f) : lambda f g p x ∈ Z g := by
    change lambda f g p x ∈ (Z g : Set (N g))
    rw [hZ]
    obtain ⟨e, k, a, he, ha, h⟩ := p
    apply degreeZeroImage 𝒜 𝓜 hsmul f.val.1 g.val.1 f.val.2 g.val.2
      f.prop.2 g.prop.2 e k a ha h (lambda f g ⟨e, k, a, he, ha, h⟩)
      (hformula f g ⟨e, k, a, he, ha, h⟩ e a h)
    change (x : N f) ∈ _
    rw [← hZ]
    exact x.prop
  let rho (f g : F) (p : Rel f g) : Z f →+ Z g :=
    { toFun := fun x ↦ ⟨lambda f g p x, hpres f g p x⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y ↦ Subtype.ext (map_add _ _ _) }
  have hrpres (f g : F) (p : Rel f g) (r : R f) :
      ∃ t : R g, t.val = lambdaS f g p r.val := by
    obtain ⟨e, k, a, he, ha, h⟩ := p
    exact homogeneousRingImage 𝒜 f.val.1 g.val.1 f.val.2 g.val.2
      f.prop.2 g.prop.2 e k a ha h (lambdaS f g ⟨e, k, a, he, ha, h⟩)
      (hring f g ⟨e, k, a, he, ha, h⟩) r
  choose rmap hrmap using hrpres
  let rhoS (f g : F) (p : Rel f g) : R f →+* R g :=
    { toFun := rmap f g p
      map_one' := by
        apply HomogeneousLocalization.val_injective (Submonoid.powers g.val.1)
        rw [hrmap, HomogeneousLocalization.val_one, map_one,
          HomogeneousLocalization.val_one]
      map_mul' := by
        intro x y
        apply HomogeneousLocalization.val_injective (Submonoid.powers g.val.1)
        rw [hrmap, HomogeneousLocalization.val_mul, map_mul,
          HomogeneousLocalization.val_mul, hrmap, hrmap]
      map_zero' := by
        apply HomogeneousLocalization.val_injective (Submonoid.powers g.val.1)
        rw [hrmap, HomogeneousLocalization.val_zero, map_zero,
          HomogeneousLocalization.val_zero]
      map_add' := by
        intro x y
        apply HomogeneousLocalization.val_injective (Submonoid.powers g.val.1)
        rw [hrmap, HomogeneousLocalization.val_add, map_add,
          HomogeneousLocalization.val_add, hrmap, hrmap] }
  let U (f g : F) : R f :=
    HomogeneousLocalization.Away.isLocalizationElem f.prop.2 g.prop.2
  refine ⟨Z, hZ, lambda, lambdaS, rho, rhoS, U, fun f g ↦ rfl, ?_⟩
  intro f g p
  refine ⟨hunit f g p, hbij f g p, ?_, hnum f g p, huniq f g p, ?_, hring f g p,
    hsemi f g p, fun x ↦ rfl, hrmap f g p, ?_, ?_⟩
  · intro e k a he ha h
    exact hinv f g p e a h
  · intro e k a he ha h
    exact hformula f g p e a h
  · intro r x
    apply Subtype.ext
    change lambda f g p ((r • x : Z f) : N f) =
      ((rhoS f g p r • rho f g p x : Z g) : N g)
    change lambda f g p (r.val • (x : N f)) =
      (rhoS f g p r).val • lambda f g p (x : N f)
    rw [hsemi]
    exact congrArg (fun r : L g ↦ r • lambda f g p (x : N f))
      (hrmap f g p r).symm
  · let v : R g := U g f
    apply isUnit_iff_exists_inv.mpr
    refine ⟨v, ?_⟩
    apply HomogeneousLocalization.val_injective (Submonoid.powers g.val.1)
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
    have huval (f g : F) : (U f g).val =
        Localization.mk (g.val.1 ^ f.val.2)
          (⟨f.val.1 ^ g.val.2, ⟨g.val.2, rfl⟩⟩ : Submonoid.powers f.val.1) := rfl
    have hv : algebraMap S (L g) (g.val.1 ^ f.val.2) * v.val =
        algebraMap S (L g) (f.val.1 ^ g.val.2) := by
      rw [huval g f, Localization.mk_eq_mk']
      exact IsLocalization.mk'_spec' (L g) _ _
    have hu : (rhoS f g p (U f g)).val *
        algebraMap S (L g) (f.val.1 ^ g.val.2) =
          algebraMap S (L g) (g.val.1 ^ f.val.2) := by
      change (rmap f g p (U f g)).val * _ = _
      rw [hrmap, ← hring f g p, ← map_mul, huval, Localization.mk_eq_mk',
        IsLocalization.mk'_spec, hring]
    have hfunit : IsUnit (algebraMap S (L g) (f.val.1 ^ g.val.2)) := by
      rw [map_pow]
      exact (hunit f g p).pow _
    apply hfunit.mul_left_cancel
    calc
      algebraMap S (L g) (f.val.1 ^ g.val.2) *
          ((rhoS f g p (U f g)).val * v.val) =
          ((rhoS f g p (U f g)).val *
            algebraMap S (L g) (f.val.1 ^ g.val.2)) * v.val := by ring
      _ = algebraMap S (L g) (f.val.1 ^ g.val.2) := by rw [hu, hv]
      _ = algebraMap S (L g) (f.val.1 ^ g.val.2) * 1 := (mul_one _).symm

end LocalizedModule
