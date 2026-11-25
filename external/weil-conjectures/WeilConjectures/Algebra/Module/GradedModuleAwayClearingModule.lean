/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# GradedModuleAwayClearingModule

Source: Stacks Project, Constructions, Lemma 01M4.
-/

@[expose] public section

universe u v

namespace LocalizedModule

set_option linter.unusedVariables false in
/-- Clearing denominators for degree-zero module restriction maps.
Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open), (1)(h).
(blueprint: lem-weil-pbc-graded-module-away-clearing-module)

Proof: If g is nilpotent, M_g and its submodule Z_g are zero; choose n = 0 and x = 0.
Otherwise represent y in Z_g as v/g^n with numerator and denominator of equal degree,
using hZ. Since g^n is nonzero, directness of the ring grading identifies their common
degree with n*deg(g). Set d = deg(f), delta = deg(g), and V = g^(n*(d-1)) • v.
The grading compatibility puts V in module degree n*d*delta. Thus the fraction
V/f^(n*delta) belongs to Z_f by hZ. In M_g, lambdaS(U) = g^d/f^delta: a ring map
preserving S sends the inverse of f to its inverse. Semilinearity of lambda, its
value on v/1, and invertibility of f give lambda(V/f^(n*delta)) = V/f^(n*delta).
This equals (g^d/f^delta)^n • (v/g^n), since d > 0 and
n*(d-1)+n = n*d. Compatibility of rho and rhoS with the ambient maps transfers
this equality to Z_g; its inclusion into M_g is injective. This supplies x and n.
No cancellation in S or M is used: only f and g are canceled in M_g, where they
act invertibly. Zero numerators and n = 0 are included in the calculation. -/
theorem gradedModuleAwayClearingModule
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
      (∀ y : Z g, ∃ (n : ℕ) (x : Z f),
        (rhoS f g p (U f g)) ^ n • y = rho f g p x) := by
  dsimp only
  intro Z hZ lambda lambdaS rho rhoS U h f g p y
  obtain ⟨hU, hmaps⟩ := h
  obtain ⟨hfunit, _, _, hlambda, _, _, hlambdaS, _, hrho, hrhoS, _, _⟩ := hmaps f g p
  have hy : (y : LocalizedModule.Away g.val.1 M) ∈ degreeZeroFractions
      (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
      (Submonoid.powers g.val.1) := by
    rw [← hZ g]
    exact y.property
  obtain ⟨j, v, s, hv, hs, hvs⟩ := hy
  obtain ⟨n, hn⟩ := s.property
  have hsval : s = (⟨g.val.1 ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g.val.1) :=
    Subtype.ext hn.symm
  subst s
  by_cases hzero : g.val.1 ^ n = 0
  · have : Subsingleton (LocalizedModule.Away g.val.1 M) :=
      LocalizedModule.subsingleton ⟨n, hzero⟩
    refine ⟨0, 0, ?_⟩
    apply Subtype.ext
    exact Subsingleton.elim _ _
  have hj : j = n * g.val.2 := by
    exact DirectSum.degree_eq_of_mem_mem 𝒜 hs
      (by simpa [nsmul_eq_mul] using SetLike.pow_mem_graded n g.property.2) hzero
  subst j
  have hexp : n * (f.val.2 - 1) + n = n * f.val.2 := by
    calc
      _ = n * ((f.val.2 - 1) + 1) := by ring
      _ = n * f.val.2 := by rw [Nat.sub_add_cancel (by have := f.property.1; omega)]
  let V : M := g.val.1 ^ (n * (f.val.2 - 1)) • v
  have hV : V ∈ 𝓜 ((n * g.val.2 * f.val.2 : ℕ) : ℤ) := by
    have hp : g.val.1 ^ (n * (f.val.2 - 1)) ∈
        𝒜 (n * (f.val.2 - 1) * g.val.2) := by
      simpa [nsmul_eq_mul] using
        SetLike.pow_mem_graded (n * (f.val.2 - 1)) g.property.2
    have ht := hsmul _ _ _ _ hp hv
    have he : ((n * (f.val.2 - 1) * g.val.2 : ℕ) : ℤ) +
        ((n * g.val.2 : ℕ) : ℤ) = ((n * g.val.2 * f.val.2 : ℕ) : ℤ) := by
      exact_mod_cast (show n * (f.val.2 - 1) * g.val.2 + n * g.val.2 =
        n * g.val.2 * f.val.2 by rw [← add_mul, hexp]; ring)
    exact he ▸ ht
  let t : Submonoid.powers f.val.1 := ⟨f.val.1 ^ (n * g.val.2), ⟨n * g.val.2, rfl⟩⟩
  have hx : mk V t ∈ Z f := by
    change mk V t ∈ (Z f : Set (LocalizedModule.Away f.val.1 M))
    rw [hZ f]
    refine ⟨n * g.val.2 * f.val.2, V, t, hV, ?_, rfl⟩
    simpa [nsmul_eq_mul] using SetLike.pow_mem_graded (n * g.val.2) f.property.2
  refine ⟨n, ⟨mk V t, hx⟩, ?_⟩
  apply Subtype.ext
  change (algebraMap (HomogeneousLocalization.Away 𝒜 g.val.1)
      (Localization.Away g.val.1) ((rhoS f g p (U f g)) ^ n)) •
      (y : LocalizedModule.Away g.val.1 M) =
      (rho f g p ⟨mk V t, hx⟩ : LocalizedModule.Away g.val.1 M)
  rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_pow,
    hrhoS, hrho]
  rw [← hvs]
  have hscalar : algebraMap S (Localization.Away g.val.1) (f.val.1 ^ g.val.2) *
      lambdaS f g p (U f g).val =
      algebraMap S (Localization.Away g.val.1) (g.val.1 ^ f.val.2) := by
    have he : algebraMap S (Localization.Away f.val.1) (f.val.1 ^ g.val.2) *
        (U f g).val =
        algebraMap S (Localization.Away f.val.1) (g.val.1 ^ f.val.2) := by
      rw [hU, Localization.mk_eq_mk', mul_comm]
      exact IsLocalization.mk'_spec _ _ _
    have he' := congrArg (lambdaS f g p) he
    simpa only [map_mul, hlambdaS] using he'
  have hscalarPow : algebraMap S (Localization.Away g.val.1)
      (f.val.1 ^ (n * g.val.2)) * (lambdaS f g p (U f g).val) ^ n =
      algebraMap S (Localization.Away g.val.1) (g.val.1 ^ (n * f.val.2)) := by
    have he := congrArg (fun r : Localization.Away g.val.1 ↦ r ^ n) hscalar
    simpa only [mul_pow, ← map_pow, ← pow_mul, Nat.mul_comm g.val.2 n,
      Nat.mul_comm f.val.2 n] using he
  apply (hfunit.pow (n * g.val.2)).smul_left_cancel.mp
  rw [← map_pow]
  calc
    _ = (algebraMap S (Localization.Away g.val.1) (f.val.1 ^ (n * g.val.2)) *
        (lambdaS f g p (U f g).val) ^ n) •
        mk v (⟨g.val.1 ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g.val.1) := by
      rw [mul_smul]
    _ = mk (g.val.1 ^ (n * f.val.2) • v)
        (⟨g.val.1 ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g.val.1) := by
      rw [hscalarPow, algebraMap_smul, smul'_mk]
    _ = mk V (1 : Submonoid.powers g.val.1) := by
      apply mk_eq.mpr
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def]
      dsimp only [V]
      rw [← mul_smul, ← pow_add, Nat.add_comm n, hexp]
    _ = lambda f g p (mk V (1 : Submonoid.powers f.val.1)) := (hlambda V).symm
    _ = algebraMap S (Localization.Away g.val.1) (f.val.1 ^ (n * g.val.2)) •
        lambda f g p (mk V t) := by
      rw [algebraMap_smul, ← map_smul, smul'_mk]
      congr 1
      exact (mk_cancel t V).symm

end LocalizedModule
