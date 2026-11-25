/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.Tactic.Ring

/-!
# GradedModuleAwayClearingRing

Source: Stacks Project, Constructions, Lemma 01M4.
-/

@[expose] public section

universe u v

namespace LocalizedModule

set_option linter.unusedVariables false in
/-- Clearing denominators for degree-zero ring restriction maps.
Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open), (1)(e).
(blueprint: lem-weil-pbc-graded-module-away-clearing-ring)

Proof: Mathlib's homogeneous fraction representation, including its nilpotent
case, gives y = b/g^n with b of degree n*deg(g). Write deg(f) = d+1 and put
B = g^(n*d)*b. Graded multiplication gives B degree n*deg(g)*deg(f), so the
explicit fraction x = B/f^(n*deg(g)) lies in R_f. Applying lambdaS to the
localization fraction equation gives lambdaS(c/f^m)*(f/1)^m = c/1, since
lambdaS preserves S. Apply this to x and U and raise the latter equation to n.
Together with y*(g/1)^n = b/1, commutative multiplication and
(d+1)*n = n*d+n prove the desired ambient equality after multiplication by
(f/1)^(n*deg(g)) and (g/1)^n. Both factors are units, so cancellation is valid
also with zero divisors or nilpotent g. Compatibility with rhoS and injectivity
of the value map give the equality in R_g. The witness is explicitly constructed;
no arbitrary object is chosen from an unproved existence theorem. -/
theorem gradedModuleAwayClearingRing
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
    ∀ (f g : F) (p : Rel f g),
      (∀ y : R g, ∃ (n : ℕ) (x : R f),
        (rhoS f g p (U f g)) ^ n * y = rhoS f g p x) := by
  dsimp
  intro Z hZ lambda lambdaS rho rhoS U h f g p y
  rcases h.2 f g p with ⟨hu, hb, hi, hl, huniq, hformula, hls, hsemi, hrho, hrs,
    hrsem, hunit⟩
  obtain ⟨n, b, hbdeg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 g.property.2 y
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt f.property.1)
  change f.val.2 = d + 1 at hd
  have hB : g.val.1 ^ (n * d) * b ∈ 𝒜 ((n * g.val.2) • f.val.2) := by
    convert SetLike.mul_mem_graded (SetLike.pow_mem_graded (n * d) g.property.2)
      hbdeg using 1
    congr 1
    simp only [nsmul_eq_mul, hd, Nat.cast_id]
    ring
  let x := HomogeneousLocalization.Away.mk 𝒜 f.property.2 (n * g.val.2)
    (g.val.1 ^ (n * d) * b) hB
  refine ⟨n, x, ?_⟩
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow, HomogeneousLocalization.val_mul, hrs]
  have hfrac (a : S) (m : ℕ) :
      lambdaS f g p (Localization.mk a
        (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1)) *
        (algebraMap S (Localization.Away g.val.1) f.val.1) ^ m =
        algebraMap S (Localization.Away g.val.1) a := by
    have he := congrArg (lambdaS f g p)
      (IsLocalization.mk'_spec (Localization.Away f.val.1) a
        (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1))
    simpa only [← Localization.mk_eq_mk', map_mul, hls, map_pow, Subtype.coe_mk] using he
  have hU := hfrac (g.val.1 ^ f.val.2) g.val.2
  rw [← h.1 f g, map_pow] at hU
  have hUn := congrArg (fun z ↦ z ^ n) hU
  simp only [mul_pow, ← pow_mul] at hUn
  have hy := IsLocalization.mk'_spec (Localization.Away g.val.1) b
    (⟨g.val.1 ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g.val.1)
  simp only [← Localization.mk_eq_mk', map_pow] at hy
  have hx := hfrac (g.val.1 ^ (n * d) * b) (n * g.val.2)
  apply (hu.pow (n * g.val.2)).mul_right_cancel
  apply (IsLocalization.map_units (Localization.Away g.val.1)
    (⟨g.val.1 ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g.val.1)).mul_right_cancel
  simp only [map_pow, HomogeneousLocalization.Away.val_mk]
  change (_ * _ * _ * _) =
    lambdaS f g p (Localization.mk (g.val.1 ^ (n * d) * b)
      (⟨f.val.1 ^ (n * g.val.2), ⟨n * g.val.2, rfl⟩⟩ :
        Submonoid.powers f.val.1)) * _ * _
  rw [hx]
  calc
    _ = ((lambdaS f g p (U f g).val) ^ n *
          (algebraMap S (Localization.Away g.val.1) f.val.1) ^ (g.val.2 * n)) *
        (Localization.mk b (⟨g.val.1 ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g.val.1) *
          (algebraMap S (Localization.Away g.val.1) g.val.1) ^ n) := by
      rw [Nat.mul_comm g.val.2 n]
      ring
    _ = (algebraMap S (Localization.Away g.val.1) g.val.1) ^ (f.val.2 * n) *
        algebraMap S (Localization.Away g.val.1) b := by rw [hUn, hy]
    _ = _ := by
      simp only [map_mul, map_pow, hd]
      rw [show (d + 1) * n = n * d + n by ring, pow_add]
      ring

end LocalizedModule
