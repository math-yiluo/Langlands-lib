/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.Algebra.Module.LocalizedModule.Away
import WeilConjectures.Algebra.Module.GradedModuleAwayClearing
import WeilConjectures.Algebra.Module.GradedModuleAwayKernel

/-!
# GradedModuleAwayComparison

Source: Stacks Project, Constructions, Lemma 01M4.
-/

@[expose] public section

universe u v

namespace LocalizedModule

private theorem comparisonOfClearing
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : Type*} [AddCommGroup Q] [Module B Q]
    (r : A →+* B) (f : P →+ Q) (u : A)
    (hf : ∀ a x, f (a • x) = r a • f x) (hu : IsUnit (r u))
    (hs : ∀ y : Q, ∃ n x, (r u) ^ n • y = f x)
    (hk : ∀ x : P, f x = 0 → ∃ n : ℕ, u ^ n • x = 0)
    (hsR : ∀ y : B, ∃ (n : ℕ) (x : A), (r u) ^ n * y = r x)
    (hkR : ∀ x : A, r x = 0 → ∃ n : ℕ, u ^ n * x = 0) :
    ∃ (t : LocalizedModule.Away u P ≃+ Q) (tR : Localization.Away u ≃+* B),
      (∀ a, tR (algebraMap A (Localization.Away u) a) = r a) ∧
      (∀ x, t (mk x 1) = f x) ∧
      (∀ (x : P) (k : ℕ), (r u) ^ k •
        t (mk x (⟨u ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers u)) = f x) ∧
      (∀ (a : Localization.Away u) (x : LocalizedModule.Away u P),
        t (a • x) = tR a • t x) := by
  classical
  let algebraAB : Algebra A B := r.toAlgebra
  let moduleAQ : Module A Q := Module.compHom Q r
  have hsm (a : A) (x : Q) : a • x = r a • x := rfl
  let l : P →ₗ[A] Q := { f with map_smul' := hf }
  have hunit : IsUnit (algebraMap A (Module.End A Q) u) := by
    rw [Module.End.isUnit_iff]
    exact hu.smul_bijective
  let : IsLocalizedModule.Away u l :=
    IsLocalizedModule.Away.mk_of_addCommGroup hunit
      (by
        intro y
        obtain ⟨n, x, hx⟩ := hs y
        refine ⟨n, x, ?_⟩
        change r (u ^ n) • y = f x
        simpa only [map_pow] using hx) hk
  let : IsLocalization.Away u B := by
    constructor
    constructor
    · rintro ⟨_, n, rfl⟩
      simpa only [RingHom.algebraMap_toAlgebra, map_pow] using hu.pow n
    · intro y
      obtain ⟨n, a, ha⟩ := hsR y
      refine ⟨⟨a, ⟨u ^ n, ⟨n, rfl⟩⟩⟩, ?_⟩
      simpa only [RingHom.algebraMap_toAlgebra, map_pow, mul_comm] using ha
    · intro a b hab
      change r a = r b at hab
      obtain ⟨n, hn⟩ := hkR (a - b) (by simp [hab])
      exact ⟨⟨u ^ n, ⟨n, rfl⟩⟩, by simpa [mul_sub, sub_eq_zero] using hn⟩
  let t := IsLocalizedModule.iso (Submonoid.powers u) l
  let tR := IsLocalization.algEquiv (Submonoid.powers u) (Localization.Away u) B
  have ht (x : P) : t (mk x 1) = f x := IsLocalizedModule.iso_mk_one _ _ x
  have htR (a : A) : tR (algebraMap A (Localization.Away u) a) = r a :=
    tR.commutes a
  refine ⟨t.toAddEquiv, tR.toRingEquiv, htR, ht, ?_, ?_⟩
  · intro x k
    change (r u) ^ k • t (mk x _) = f x
    rw [← map_pow, ← hsm]
    rw [← t.map_smul]
    rw [smul'_mk]
    change t (mk ((u ^ k) • x) _) = f x
    exact (congrArg t (mk_cancel
      (⟨u ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers u) x)).trans (ht x)
  · intro a x
    obtain ⟨⟨b, s⟩, hab⟩ := IsLocalization.surj (Submonoid.powers u) a
    have huS : IsUnit (r s) := IsLocalization.map_units B s
    apply huS.smul_left_cancel.mp
    change r s • t (a • x) = r s • (tR a • t x)
    calc
      r s • t (a • x) = t ((s : A) • (a • x)) := by
        simpa only [hsm] using (t.map_smul (s : A) _).symm
      _ = t ((b : A) • x) := by
        congr 1
        rw [← algebraMap_smul (Localization.Away u) (s : A), smul_smul,
          mul_comm, hab, algebraMap_smul]
      _ = r b • t x := by simpa only [hsm] using t.map_smul b x
      _ = r s • (tR a • t x) := by
        rw [smul_smul, ← htR s, ← map_mul, mul_comm, hab, htR]

set_option linter.unusedVariables false in
/-- Principal localization comparisons for a fixed family of restriction maps.
Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open), proof of
(1)(e),(h), and the fraction formulas in its proof.
(blueprint: lem-weil-pbc-graded-module-away-comparison)

Proof: Restrict scalars on Z g along rhoS. The unit rhoS(U) makes multiplication by U
invertible, so the module and ring universal properties give theta and thetaS with the
stated formulas. Semilinearity follows by multiplying fractions. For surjectivity, if
y/g^n has degree zero, put d = deg f and delta = deg g. Then
Y = g^(n*(d-1))*y has degree n*d*delta, and z = Y/f^(n*delta) lies in Z f.
The image of z/U^n is Y/g^(n*d) = y/g^n. For injectivity, a fraction z/U^k mapping to
zero, with z = x/f^m, satisfies g^N*a^m*x = 0 for some N. Multiplication by f^m gives
g^(N+e*m)*x = 0. Choose K with K*d at least N+e*m; then U^K*z = 0, so z/U^k = 0.
The ring case is the same computation. These bijections give the two equivalences.
Nilpotent denominators give zero modules throughout. -/
theorem gradedModuleAwayComparison
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
    ∀ (Z : ∀ f : F, Submodule (R f) (N f)),
      (∀ f : F, (Z f : Set (N f)) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)) →
    ∀ (lambda : ∀ (f g : F), Rel f g → N f →ₗ[S] N g)
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
        IsUnit (rhoS f g p (U f g))) →
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
          theta f g p (r • x) = thetaS f g p r • theta f g p x)) := by
  classical
  dsimp only
  intro Z hZ lambda lambdaS rho rhoS U h
  have hs := gradedModuleAwayClearing 𝒜 𝓜 h𝓜 hsmul Z hZ lambda lambdaS rho rhoS U h
  have hk := gradedModuleAwayKernel 𝒜 𝓜 h𝓜 hsmul Z hZ lambda lambdaS rho rhoS U h
  have hp (f g : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2})
      (p : ∃ (e k : ℕ) (a : S),
        0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1) :=
    comparisonOfClearing (rhoS f g p) (rho f g p) (U f g)
      (h.2 f g p).2.2.2.2.2.2.2.2.2.2.1 (h.2 f g p).2.2.2.2.2.2.2.2.2.2.2
      (hs f g p).1 (hk f g p).1 (hs f g p).2 (hk f g p).2
  choose theta thetaS htheta using hp
  exact ⟨theta, thetaS, htheta⟩

end LocalizedModule
