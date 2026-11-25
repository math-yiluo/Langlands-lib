/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.Algebra.Module.GradedModuleAwayClearingModule
import WeilConjectures.Algebra.Module.GradedModuleAwayClearingRing

/-!
# GradedModuleAwayClearing

Source: Stacks Project, Constructions, Lemma 01M4.
-/

@[expose] public section

universe u v

namespace LocalizedModule

set_option linter.unusedVariables false in
/-- Clearing denominators for degree-zero module and ring restriction maps.
Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open), (1)(e),(h).
(blueprint: lem-weil-pbc-graded-module-away-clearing)

Proof: If g is nilpotent, the target localizations are zero and take n = 0, x = 0.
Otherwise hZ represents a target module fraction as y/g^n with y and g^n of the
same degree. Directness of the ring grading and g^n != 0 identify that degree
with n*delta, so y is homogeneous of degree n*delta.
Put d = deg f > 0 and Y = g^(n*(d-1)) • y. Then Y has degree n*d*delta,
so Y/f^(n*delta) belongs to Z f. Multiplying y/g^n by rhoS(U)^n gives
rho(Y/f^(n*delta)): apply the given lambda fraction formula and cancel f,
which is invertible in the target localization. For a ring fraction use the
same construction with multiplication in S. The homogeneous localization's
fraction representation supplies homogeneous ring numerators. The ring map
lambdaS sends b/f^m to b*(a/g^e)^m: it preserves the image of S and sends the
inverse of f/1 to its inverse, which the hypotheses identify as a/g^e.
Thus it sends U to g^d/f^delta in L g. Equality in the ordinary localizations
implies equality in Z g and R g by injectivity of their inclusions. These identities
hold also for nilpotent denominators, since localization and its submodules
are then zero. No domain or nonzero numerator assumption is used. -/
theorem gradedModuleAwayClearing
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
        (rhoS f g p (U f g)) ^ n • y = rho f g p x) ∧
      (∀ y : R g, ∃ (n : ℕ) (x : R f),
        (rhoS f g p (U f g)) ^ n * y = rhoS f g p x) := by
  dsimp
  intro Z hZ lambda lambdaS rho rhoS U h f g p
  exact ⟨gradedModuleAwayClearingModule 𝒜 𝓜 h𝓜 hsmul Z hZ lambda lambdaS rho rhoS U h f g p,
    gradedModuleAwayClearingRing 𝒜 𝓜 h𝓜 hsmul Z hZ lambda lambdaS rho rhoS U h f g p⟩

end LocalizedModule
