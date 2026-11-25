/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.Algebra.Module.GradedModuleAwayMaps
import WeilConjectures.Algebra.Module.GradedModuleAwayComparison

/-!
# Restriction maps between degree-zero graded module localizations

Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open),
parts (1)(a),(c),(d),(e),(g),(h); Algebra, Section 00JM
(blueprint: lem-weil-pbc-graded-module-away-restriction).
-/

@[expose] public section

universe u v

namespace LocalizedModule

set_option linter.unusedVariables false in
/-- Restriction maps, their principal localization comparisons, and compatibility.
The positive homogeneous elements are indexed by `F`; `Rel f g` records a homogeneous
relation `g ^ e = a * f`. The submodules `Z f` have exactly the equal-degree fractions
as carriers; the scalar action is restricted from the ordinary localized module.

Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open).
(blueprint: lem-weil-pbc-graded-module-away-restriction)

Proof:
1. If the target denominator is nilpotent, its localizations are zero; otherwise the
   grading determines the degree of the homogeneous multiplier in the relation.
2. Apply the ordinary module localization universal property: `f` is a unit after
   localizing at `g`, with inverse `a / g ^ e`. This gives the unique map `lambda`.
3. Its fraction formula gives the ring map `lambdaS` and semilinearity.
4. Degree bookkeeping restricts these maps to `rho` and `rhoS` on equal-degree fractions.
5. Uniqueness gives identity and composition, independently of the relation witnesses.
6. The image of `u = g ^ deg f / f ^ deg g` is a unit, with inverse
   `f ^ deg g / g ^ deg f` in the target degree-zero ring.
7. The module localization universal property gives `theta`, and the ring version gives
   `thetaS`, with their fraction formula and semilinearity.
8. For surjectivity, rewrite `y / g ^ n` as `g ^ (n * (deg f - 1)) y / g ^ (n * deg f)`.
9. For injectivity, a target-zero fraction is killed by a power of `g`, hence by a power
   of `u` before the second localization. Thus both comparison maps are isomorphisms.
10. For a third denominator `h`, transitivity and the ring isomorphism make `u` a unit
    after localizing at `u'`; the fraction formulas give the canonical map `kappa` and
    the commuting square. These use the three localization definition dependencies.
-/
theorem gradedModuleAwayRestriction
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
        IsUnit (rhoS f g p (U f g))) ∧
      (∀ (f : F) (p : Rel f f),
        (∀ x : Z f, rho f f p x = x) ∧ (∀ r : R f, rhoS f f p r = r)) ∧
      (∀ (f g h : F) (e e' : ℕ) (a a' : S),
        g.val.1 ^ e = a * f.val.1 → h.val.1 ^ e' = a' * g.val.1 →
        h.val.1 ^ (e * e') = (a' ^ e * a) * f.val.1) ∧
      (∀ (f g h : F) (p : Rel f g) (q : Rel g h), Rel f h ∧
        ∀ t : Rel f h,
          (∀ x : Z f, rho g h q (rho f g p x) = rho f h t x) ∧
          (∀ r : R f, rhoS g h q (rhoS f g p r) = rhoS f h t r)) ∧
    ∃ (theta : ∀ (f g : F), Rel f g → LocalizedModule.Away (U f g) (Z f) ≃+ Z g)
      (thetaS : ∀ (f g : F), Rel f g → Localization.Away (U f g) ≃+* R g),
      (∀ (f g : F) (p : Rel f g),
        (∀ r : R f, thetaS f g p (algebraMap (R f) (Localization.Away (U f g)) r) =
          rhoS f g p r) ∧
        (∀ x : Z f, theta f g p (mk x 1) = rho f g p x) ∧
        (∀ (x : Z f) (k : ℕ), (rhoS f g p (U f g)) ^ k •
          theta f g p (mk x (⟨(U f g) ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers (U f g))) =
            rho f g p x) ∧
        (∀ (r : Localization.Away (U f g)) (x : LocalizedModule.Away (U f g) (Z f)),
          theta f g p (r • x) = thetaS f g p r • theta f g p x)) ∧
      (∀ (f g h : F) (p : Rel f g) (q : Rel g h) (t : Rel f h),
        IsUnit (algebraMap (R f) (Localization.Away (U f h)) (U f g)) ∧
        ∃ kappa : LocalizedModule.Away (U f g) (Z f) →ₗ[R f]
          LocalizedModule.Away (U f h) (Z f),
          (∀ x : Z f, kappa (mk x 1) = mk x 1) ∧
          (∀ K : LocalizedModule.Away (U f g) (Z f) →ₗ[R f]
            LocalizedModule.Away (U f h) (Z f),
            (∀ x : Z f, K (mk x 1) = mk x 1) → K = kappa) ∧
          (∀ x : LocalizedModule.Away (U f g) (Z f),
            rho g h q (theta f g p x) = theta f h t (kappa x))) := by
  classical
  dsimp only
  obtain ⟨Z, hZ, lambda, lambdaS, rho, rhoS, U, hU, hpair⟩ :=
    gradedModuleAwayMaps 𝒜 𝓜 h𝓜 hsmul
  let F := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
  let Rel := fun f g : F ↦ ∃ (e k : ℕ) (a : S),
    0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1
  have hrel (f g h : F) (p : Rel f g) (q : Rel g h) : Rel f h := by
    obtain ⟨e, k, a, he, ha, hfg⟩ := p
    obtain ⟨e', k', a', he', ha', hgh⟩ := q
    refine ⟨e * e', e * k' + k, a' ^ e * a, Nat.mul_pos he he', ?_, ?_⟩
    · simpa [Nat.mul_comm] using
        SetLike.mul_mem_graded (SetLike.pow_mem_graded e ha') ha
    · rw [mul_comm e e', pow_mul, hgh, mul_pow, hfg, mul_assoc]
  have hcomp (f g h : F) (p : Rel f g) (q : Rel g h) (t : Rel f h) :
      (∀ x : Z f, rho g h q (rho f g p x) = rho f h t x) ∧
      (∀ r : HomogeneousLocalization.Away 𝒜 f.val.1,
        rhoS g h q (rhoS f g p r) = rhoS f h t r) := by
    rcases hpair f g p with ⟨_, _, _, hfg, _, _, hSfg, _, hrfg, hRSfg, _, _⟩
    rcases hpair g h q with ⟨_, _, _, hgh, _, _, hSgh, _, hrgh, hRSgh, _, _⟩
    rcases hpair f h t with ⟨_, _, _, _, huniq, _, hSfh, _, hrfh, hRSfh, _, _⟩
    have hl : (lambda g h q).comp (lambda f g p) = lambda f h t := by
      apply huniq
      intro x
      simp only [LinearMap.comp_apply, hfg, hgh]
    have hs : (lambdaS g h q).comp (lambdaS f g p) = lambdaS f h t := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f.val.1)
      ext x
      simp only [RingHom.comp_apply, hSfg, hSgh, hSfh]
    constructor
    · intro x
      apply Subtype.ext
      rw [hrgh, hrfg, hrfh]
      exact LinearMap.congr_fun hl x
    · intro r
      apply HomogeneousLocalization.val_injective
      rw [hRSgh, hRSfg, hRSfh]
      exact RingHom.congr_fun hs r.val
  have hid (f : F) (p : Rel f f) :
      (∀ x : Z f, rho f f p x = x) ∧
      (∀ r : HomogeneousLocalization.Away 𝒜 f.val.1, rhoS f f p r = r) := by
    rcases hpair f f p with ⟨_, _, _, _, huniq, _, hS, _, hr, hRS, _, _⟩
    have hl : LinearMap.id = lambda f f p := huniq LinearMap.id (fun _ ↦ rfl)
    have hs : RingHom.id _ = lambdaS f f p := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f.val.1)
      ext x
      exact (hS x).symm
    constructor
    · intro x
      apply Subtype.ext
      rw [hr, ← hl]
      rfl
    · intro r
      apply HomogeneousLocalization.val_injective
      rw [hRS, ← hs]
      rfl
  obtain ⟨theta, thetaS, htheta⟩ :=
    gradedModuleAwayComparison 𝒜 𝓜 h𝓜 hsmul Z hZ lambda lambdaS rho rhoS U
      ⟨hU, hpair⟩
  have htheta_smul (f g : F) (p : Rel f g)
      (r : HomogeneousLocalization.Away 𝒜 f.val.1)
      (x : LocalizedModule.Away (U f g) (Z f)) :
      theta f g p (r • x) = rhoS f g p r • theta f g p x := by
    have hh := (htheta f g p).2.2.2
      (algebraMap _ (Localization.Away (U f g)) r) x
    rw [(htheta f g p).1] at hh
    simpa only [algebraMap_smul] using hh
  have hkappa (f g h : F) (p : Rel f g) (q : Rel g h) (t : Rel f h) :
      IsUnit (algebraMap _ (Localization.Away (U f h)) (U f g)) ∧
      ∃ kappa : LocalizedModule.Away (U f g) (Z f) →ₗ[HomogeneousLocalization.Away 𝒜 f.val.1]
        LocalizedModule.Away (U f h) (Z f),
        (∀ x : Z f, kappa (mk x 1) = mk x 1) ∧
        (∀ K : LocalizedModule.Away (U f g) (Z f) →ₗ[HomogeneousLocalization.Away 𝒜 f.val.1]
          LocalizedModule.Away (U f h) (Z f),
          (∀ x : Z f, K (mk x 1) = mk x 1) → K = kappa) ∧
        (∀ x : LocalizedModule.Away (U f g) (Z f),
          rho g h q (theta f g p x) = theta f h t (kappa x)) := by
    let nu : Localization.Away (U f g) →+* Localization.Away (U f h) :=
      (thetaS f h t).symm.toRingHom.comp
        ((rhoS g h q).comp (thetaS f g p).toRingHom)
    have hnu (r : HomogeneousLocalization.Away 𝒜 f.val.1) :
        nu (algebraMap _ (Localization.Away (U f g)) r) =
          algebraMap _ (Localization.Away (U f h)) r := by
      change (thetaS f h t).symm (rhoS g h q
        (thetaS f g p (algebraMap _ (Localization.Away (U f g)) r))) = _
      rw [(htheta f g p).1, (hcomp f g h p q t).2,
        ← (htheta f h t).1]
      exact (thetaS f h t).symm_apply_apply _
    have hu : IsUnit (algebraMap _ (Localization.Away (U f h)) (U f g)) := by
      rw [← hnu]
      exact (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (U f g)) (U f g)).map nu
    let ka : LocalizedModule.Away (U f g) (Z f) →+ LocalizedModule.Away (U f h) (Z f) :=
      (theta f h t).symm.toAddMonoidHom.comp
        ((rho g h q).comp (theta f g p).toAddMonoidHom)
    have hka (x : LocalizedModule.Away (U f g) (Z f)) :
        theta f h t (ka x) = rho g h q (theta f g p x) := by
      exact (theta f h t).apply_symm_apply _
    let kappa : LocalizedModule.Away (U f g) (Z f) →ₗ[HomogeneousLocalization.Away 𝒜 f.val.1]
        LocalizedModule.Away (U f h) (Z f) :=
      { ka with
        map_smul' := by
          intro r x
          apply (theta f h t).injective
          change theta f h t (ka (r • x)) = theta f h t (r • ka x)
          rw [hka, htheta_smul, (hpair g h q).2.2.2.2.2.2.2.2.2.2.1,
            (hcomp f g h p q t).2, htheta_smul]
          rw [hka] }
    have hkone (x : Z f) : kappa (mk x 1) = mk x 1 := by
      apply (theta f h t).injective
      change theta f h t (ka (mk x 1)) = _
      rw [hka, (htheta f g p).2.1, (hcomp f g h p q t).1,
        (htheta f h t).2.1]
    refine ⟨hu, kappa, hkone, ?_, fun x ↦ (hka x).symm⟩
    intro K hK
    refine IsLocalizedModule.ext (Submonoid.powers (U f g))
      (mkLinearMap (Submonoid.powers (U f g)) (Z f)) ?_ ?_
    · intro s
      obtain ⟨n, hn⟩ := s.property
      have hs : IsUnit (algebraMap _ (Localization.Away (U f h)) 
          (s : HomogeneousLocalization.Away 𝒜 f.val.1)) := by
        rw [← hn, map_pow]
        exact hu.pow n
      rw [Module.End.isUnit_iff]
      change Function.Bijective (fun x : LocalizedModule.Away (U f h) (Z f) ↦
        (s : HomogeneousLocalization.Away 𝒜 f.val.1) • x)
      simpa only [Module.algebraMap_end_apply, algebraMap_smul] using
        (hs.smul_bijective : Function.Bijective
          (fun x : LocalizedModule.Away (U f h) (Z f) ↦
            algebraMap _ (Localization.Away (U f h))
              (s : HomogeneousLocalization.Away 𝒜 f.val.1) • x))
    · ext x
      exact (hK x).trans (hkone x).symm
  refine ⟨Z, hZ, lambda, lambdaS, rho, rhoS, U, hU, hpair, hid, ?_, ?_,
    theta, thetaS, htheta, hkappa⟩
  · intro f g h e e' a a' hfg hgh
    rw [mul_comm e e', pow_mul, hgh, mul_pow, hfg, mul_assoc]
  · intro f g h p q
    exact ⟨hrel f g h p q, hcomp f g h p q⟩

end LocalizedModule
