/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# GradedModuleAwayKernel

Source: Stacks Project, Constructions, Lemma 01M4.
-/

@[expose] public section

universe u v

namespace LocalizedModule

/-- Clear the source denominator, then apply the target localization zero criterion.
This ordinary-localization calculation also applies to the ring regarded as a module. -/
private theorem awayKernelFraction
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
    (f g : S) (d j : ℕ) (hd : 0 < d)
    (T : LocalizedModule.Away f M →ₗ[S] LocalizedModule.Away g M)
    (hT : ∀ b : M, T (mk b 1) = mk b 1)
    (y : LocalizedModule.Away f M) (hy : T y = 0) :
    ∃ n : ℕ, (Localization.mk (g ^ d)
      (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)) ^ n • y = 0 := by
  induction y using LocalizedModule.induction_on with
  | h b s =>
    have hb : (mk b 1 : LocalizedModule.Away g M) = 0 := by
      rw [← hT]
      have hs : (s : S) • mk b s = (mk b 1 : LocalizedModule.Away f M) := by
        simpa only [smul'_mk, Submonoid.smul_def] using mk_cancel s b
      rw [← hs, T.map_smul, hy, smul_zero]
    obtain ⟨t, ht⟩ := mk_eq.mp (hb.trans (zero_mk 1).symm)
    have ht' : (t : S) • b = 0 := by simpa [Submonoid.smul_def] using ht
    obtain ⟨n, hn⟩ := t.property
    have hn' : g ^ n • b = 0 := by simpa [← hn] using ht'
    obtain ⟨d', hd'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    have hdn : (g ^ d) ^ n • b = 0 := by
      rw [← pow_mul, Nat.mul_comm, hd', Nat.mul_succ, pow_add, mul_smul,
        hn', smul_zero]
    refine ⟨n, ?_⟩
    rw [Localization.mk_pow, mk_smul_mk, hdn, zero_mk]

set_option linter.unusedVariables false in
/-- Detection of the kernel by powers of the principal comparison denominator.
Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open), (1)(e),(h).
(blueprint: lem-weil-pbc-graded-module-away-kernel)

Proof: Represent z in Z f by x/f^m and choose the homogeneous relation g^e = a*f.
If rho(z) = 0, the lambda fraction formula gives a^m • x/g^(e*m) = 0.
The ordinary localization zero criterion supplies N with g^N*a^m • x = 0.
Multiplying this equality by f^m yields g^(N+e*m) • x = 0. Since d = deg f
is positive, choose K with K*d >= N+e*m. Then g^(K*d) • x = 0, which
says U^K • z = 0 in N f and hence in its submodule Z f. For the ring
kernel the identical computation uses multiplication rather than scalar action,
the given compatibility of rhoS with lambdaS, and localization's zero criterion.
Indeed lambdaS preserves S and hence sends b/f^m to b*(a/g^e)^m, since it
preserves inverses and the given inverse of f/1 is a/g^e. The formula for U
identifies U^K*z with g^(K*d)*x/f^(K*deg g+m). The inclusions of Z f and R f
in their ordinary localizations are injective, so vanishing there suffices.
If a denominator is nilpotent the same zero criterion still applies; cancellation
in the original ring is never used. -/
theorem gradedModuleAwayKernel
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
      (∀ x : Z f, rho f g p x = 0 → ∃ n : ℕ, (U f g) ^ n • x = 0) ∧
      (∀ x : R f, rhoS f g p x = 0 → ∃ n : ℕ, (U f g) ^ n * x = 0) := by
  intro F R L N Rel Z hZ lambda lambdaS rho rhoS U h f g p
  obtain ⟨_, _, _, hbase, _, _, hbaseS, _, hrho, hrhoS, _, _⟩ := h.2 f g p
  constructor
  · intro x hx
    have hl : lambda f g p (x : N f) = 0 := by
      rw [← hrho x, hx]
      rfl
    obtain ⟨n, hn⟩ := awayKernelFraction f.val.1 g.val.1 f.val.2 g.val.2
      f.property.1 (lambda f g p) hbase (x : N f) hl
    refine ⟨n, ?_⟩
    apply Subtype.ext
    change (algebraMap (R f) (L f) ((U f g) ^ n)) • (x : N f) = 0
    rw [map_pow]
    change (U f g).val ^ n • (x : N f) = 0
    rw [h.1 f g]
    exact hn
  · intro x hx
    let T : L f →ₗ[S] L g :=
      { toFun := lambdaS f g p
        map_add' := (lambdaS f g p).map_add
        map_smul' := fun r z ↦ by
          simp only [Algebra.smul_def, map_mul, hbaseS, RingHom.id_apply] }
    have hT : ∀ b : S, T (mk b 1) = mk b 1 := by
      intro b
      change lambdaS f g p (algebraMap S (L f) b) = algebraMap S (L g) b
      exact hbaseS b
    have hl : T x.val = 0 := by
      change lambdaS f g p x.val = 0
      rw [← hrhoS x, hx, HomogeneousLocalization.val_zero]
    obtain ⟨n, hn⟩ := awayKernelFraction f.val.1 g.val.1 f.val.2 g.val.2
      f.property.1 T hT x.val hl
    refine ⟨n, ?_⟩
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      HomogeneousLocalization.val_zero, h.1 f g]
    exact hn

end LocalizedModule
