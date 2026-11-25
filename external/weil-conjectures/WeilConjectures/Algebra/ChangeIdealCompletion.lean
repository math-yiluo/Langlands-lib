/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Change of ideal for adic completion
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion) -/

@[expose] public section

open scoped Pointwise


/-- `J ^ (d * k) M ⊆ I ^ k M` when `J ^ d ⊆ I`: the inclusion making the reduction
`M/J^{dk}M → M/I^kM` of the comparison map well defined.
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion).
Proof: `J ^ (d * k) = (J ^ d) ^ k ≤ I ^ k`, and `• ⊤` is monotone in the ideal. -/
theorem powerReductionJI {A : Type*} [CommRing A] (I J : Ideal A) (d k : ℕ)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hJI : J ^ d ≤ I) :
    J ^ (d * k) • (⊤ : Submodule A M) ≤ I ^ k • (⊤ : Submodule A M) := by
  exact Submodule.smul_mono_left (by
    rw [pow_mul]
    exact pow_le_pow_left' hJI k)

/-- `I ^ (c * n) M ⊆ J ^ n M` when `I ^ c ⊆ J`: the inclusion making the reduction
`M/I^{cn}M → M/J^nM` of the inverse comparison map well defined.
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion).
Proof: `I ^ (c * n) = (I ^ c) ^ n ≤ J ^ n`, and `• ⊤` is monotone in the ideal. -/
theorem powerReductionIJ {A : Type*} [CommRing A] (I J : Ideal A) (c n : ℕ)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hIJ : I ^ c ≤ J) :
    I ^ (c * n) • (⊤ : Submodule A M) ≤ J ^ n • (⊤ : Submodule A M) := by
  exact powerReductionJI J I c n M hIJ

private def comparisonMap {A : Type*} [CommRing A] (I J : Ideal A) (d : ℕ)
    (M : Type*) [AddCommGroup M] [Module A M] (hJI : J ^ d ≤ I) :
    AdicCompletion J M →ₗ[A] AdicCompletion I M where
  toFun x := ⟨fun k ↦ Submodule.factor (powerReductionJI I J d k M hJI) (x.val (d * k)),
    fun {k l} hkl ↦ by
      have h := x.property (Nat.mul_le_mul_left d hkl)
      have hf := congrArg (Submodule.factor (powerReductionJI I J d k M hJI)) h
      simpa only [AdicCompletion.transitionMap, Submodule.factorPow,
        Submodule.factor_comp_apply] using hf⟩
  map_add' x y := by
    apply AdicCompletion.ext
    intro k
    exact map_add _ _ _
  map_smul' a x := by
    apply AdicCompletion.ext
    intro k
    exact (Submodule.factor (powerReductionJI I J d k M hJI)).map_smul a (x.val (d * k))

private theorem comparisonMap_inverse {A : Type*} [CommRing A] (I J : Ideal A)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I)
    (M : Type*) [AddCommGroup M] [Module A M] (x : AdicCompletion J M) :
    comparisonMap J I c M hIJ (comparisonMap I J d M hJI x) = x := by
  apply AdicCompletion.ext
  intro n
  have hnc : n ≤ c * n := by simpa using Nat.mul_le_mul_right n hc
  have hcd : c * n ≤ d * (c * n) := by
    simpa using Nat.mul_le_mul_right (c * n) hd
  have hn : n ≤ d * (c * n) := hnc.trans hcd
  simpa only [comparisonMap, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.factor_comp_apply, AdicCompletion.transitionMap, Submodule.factorPow]
    using x.property hn

/-- Completions for two cofinal ideals are canonically isomorphic.
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion).
Proof: the systems of maps `M/J^{dk}M → M/I^kM` and `M/I^{cn}M → M/J^nM` are
compatible with the transition maps and `A`-linear, so they give maps
`θ : M^∧_J → M^∧_I` and `θ' : M^∧_I → M^∧_J`; both composites are computed
componentwise to be the identity (`x_{cdk}` reduces to `x_k`), so `θ` is a linear
equivalence. Both `θ ∘ ι_J` and `ι_I` send `x` to `(x mod I^kM)_k`, so they agree;
hence `ι_I` is bijective iff `ι_J = θ⁻¹ ∘ ι_I` is. -/
theorem changeIdealCompletion
    {A : Type*} [CommRing A] (I J : Ideal A) (c d : ℕ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I)
    (M : Type*) [AddCommGroup M] [Module A M] :
    ∃ (θ : AdicCompletion J M ≃ₗ[A] AdicCompletion I M),
      (∀ (x : AdicCompletion J M) (k : ℕ),
        (θ x).val k =
          Submodule.factor (show J ^ (d * k) • (⊤ : Submodule A M) ≤
            I ^ k • (⊤ : Submodule A M) by exact powerReductionJI I J d k M hJI) (x.val (d * k))) ∧
      (∀ (x : AdicCompletion I M) (n : ℕ),
        (θ.symm x).val n =
          Submodule.factor (show I ^ (c * n) • (⊤ : Submodule A M) ≤
            J ^ n • (⊤ : Submodule A M) by exact powerReductionIJ I J c n M hIJ) (x.val (c * n))) ∧
      (∀ (x : M), θ (AdicCompletion.of J M x) = AdicCompletion.of I M x) ∧
      (Function.Bijective (AdicCompletion.of I M) ↔
        Function.Bijective (AdicCompletion.of J M))
    := by
  let θ : AdicCompletion J M ≃ₗ[A] AdicCompletion I M :=
    { comparisonMap I J d M hJI with
      invFun := comparisonMap J I c M hIJ
      left_inv := comparisonMap_inverse I J c d hc hd hIJ hJI M
      right_inv := comparisonMap_inverse J I d c hd hc hJI hIJ M }
  have hof : ∀ x : M, θ (AdicCompletion.of J M x) = AdicCompletion.of I M x := by
    intro x
    apply AdicCompletion.ext
    intro k
    rfl
  refine ⟨θ, fun _ _ ↦ rfl, fun _ _ ↦ rfl, hof, ?_⟩
  have hcomp : (AdicCompletion.of I M : M → AdicCompletion I M) =
      θ ∘ AdicCompletion.of J M := funext fun x ↦ (hof x).symm
  rw [hcomp]
  exact Function.Bijective.of_comp_iff' θ.bijective _


/-- For `M = A` the comparison `θ : A^∧_J → A^∧_I`, `(x_n)_n ↦ (x_{dk} mod I^k)_k`,
is a ring equivalence.
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion).
Proof: `θ` is the linear equivalence of `changeIdealCompletion` for `M = A`; each
reduction `A/J^{dk} → A/I^k` is a ring map and multiplication on both completions
is componentwise, so `θ` preserves `1` and products. -/
theorem changeIdealCompletionRing
    {A : Type*} [CommRing A] (I J : Ideal A) (c d : ℕ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    ∃ e : AdicCompletion J A ≃+* AdicCompletion I A,
      (∀ (x : AdicCompletion J A) (k : ℕ),
        (e x).val k =
          Submodule.factor (show J ^ (d * k) • (⊤ : Submodule A A) ≤
            I ^ k • (⊤ : Submodule A A) by exact powerReductionJI I J d k A hJI)
            (x.val (d * k))) := by
  obtain ⟨θ, hθ, _, _, _⟩ := changeIdealCompletion I J c d hc hd hIJ hJI A
  let e : AdicCompletion J A ≃+* AdicCompletion I A :=
    { θ.toEquiv with
      map_add' := θ.map_add
      map_mul' := fun x y ↦ by
        apply AdicCompletion.ext
        intro k
        change (θ (x * y)).val k = (θ x * θ y).val k
        rw [hθ, AdicCompletion.val_mul, AdicCompletion.val_mul, hθ, hθ]
        exact Quotient.inductionOn₂' (x.val (d * k)) (y.val (d * k))
          (fun _ _ ↦ rfl) }
  exact ⟨e, hθ⟩
