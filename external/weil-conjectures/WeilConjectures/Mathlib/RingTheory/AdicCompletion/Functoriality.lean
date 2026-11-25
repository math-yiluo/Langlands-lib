/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finiteness of modules which are adically separated for a principal ideal

Let `R` be a commutative ring which is `ϖ`-adically precomplete for an element `ϖ`. A
`ϖ`-adically separated `R`-module `N` with `N ⧸ ϖN` finitely generated is finitely generated
(`Module.Finite.of_isHausdorff_span_singleton`): lift generators of `N ⧸ ϖN` and apply
`surjective_of_mkQ_comp_surjective` to the free module they span, which is precomplete
(`IsPrecomplete.pi_span_singleton`).
-/

@[expose] public section

variable {R : Type*} [CommRing R]

/-- For a principal ideal `(ϖ)`, the submodule `(ϖ)ⁿ N` of `N` consists of the multiples
`ϖⁿ y`. -/
lemma Submodule.mem_span_singleton_pow_smul_top_iff {N : Type*} [AddCommGroup N] [Module R N]
    (ϖ : R) (n : ℕ) (x : N) :
    x ∈ (Ideal.span {ϖ}) ^ n • (⊤ : Submodule R N) ↔ ∃ y : N, ϖ ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- **Products of precomplete rings are precomplete** for a principal ideal: if `R` is
`ϖ`-adically precomplete, so is `ι → R`. -/
lemma IsPrecomplete.pi_span_singleton (ϖ : R) [IsPrecomplete (Ideal.span {ϖ}) R] (ι : Type*) :
    IsPrecomplete (Ideal.span {ϖ}) (ι → R) where
  prec' f hf := by
    have hcomp (i : ι) {m n : ℕ} (h : m ≤ n) :
        f m i ≡ f n i [SMOD ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule R R)] := by
      obtain ⟨y, hy⟩ := (Submodule.mem_span_singleton_pow_smul_top_iff ϖ m _).1
        (SModEq.sub_mem.1 (hf h))
      refine SModEq.sub_mem.2 ((Submodule.mem_span_singleton_pow_smul_top_iff ϖ m _).2
        ⟨y i, ?_⟩)
      rw [← Pi.sub_apply, ← hy, Pi.smul_apply]
    choose L hL using fun i ↦ IsPrecomplete.prec' (I := Ideal.span {ϖ}) (fun n ↦ f n i)
      (hcomp i)
    refine ⟨L, fun n ↦ SModEq.sub_mem.2 ?_⟩
    choose y hy using fun i ↦ (Submodule.mem_span_singleton_pow_smul_top_iff ϖ n _).1
      (SModEq.sub_mem.1 (hL i n))
    exact (Submodule.mem_span_singleton_pow_smul_top_iff ϖ n _).2 ⟨y, funext hy⟩

/-- **Topological Nakayama for a principal ideal.** Let `R` be `ϖ`-adically precomplete and `N`
a `ϖ`-adically separated `R`-module with `N ⧸ ϖN` finitely generated. Then `N` is finitely
generated. -/
lemma Module.Finite.of_isHausdorff_span_singleton (ϖ : R) [IsPrecomplete (Ideal.span {ϖ}) R]
    {N : Type*} [AddCommGroup N] [Module R N] [IsHausdorff (Ideal.span {ϖ}) N]
    [Module.Finite R (N ⧸ (Ideal.span {ϖ} • ⊤ : Submodule R N))] :
    Module.Finite R N := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (N ⧸ (Ideal.span {ϖ} • ⊤ : Submodule R N))
  choose s hs using fun i : Fin n ↦ Submodule.mkQ_surjective _ (g (Pi.single i 1))
  have := IsPrecomplete.pi_span_singleton ϖ (Fin n)
  let f : (Fin n → R) →ₗ[R] N := Fintype.linearCombination R s
  have hf : (Submodule.mkQ (Ideal.span {ϖ} • ⊤) ∘ₗ f) = g := by
    refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
    simp [f, hs]
  have hsurj : Function.Surjective f :=
    surjective_of_mkQ_comp_surjective (I := Ideal.span {ϖ}) (hf ▸ hg)
  exact Module.Finite.of_surjective f hsurj

/-- **Precompleteness transfers along ring isomorphisms** for principal ideals: if `R` is
`ϖ`-adically precomplete and `e : R ≃+* S`, then `S` is `e ϖ`-adically precomplete. -/
lemma IsPrecomplete.of_ringEquiv {S : Type*} [CommRing S] (e : R ≃+* S) (ϖ : R)
    [IsPrecomplete (Ideal.span {ϖ}) R] : IsPrecomplete (Ideal.span {e ϖ}) S where
  prec' f hf := by
    have key (a b : R) (n : ℕ) : a ≡ b [SMOD ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule R R)] ↔
        e a ≡ e b [SMOD ((Ideal.span {e ϖ}) ^ n • ⊤ : Submodule S S)] := by
      rw [SModEq.sub_mem, SModEq.sub_mem, ← map_sub,
        Submodule.mem_span_singleton_pow_smul_top_iff,
        Submodule.mem_span_singleton_pow_smul_top_iff]
      refine ⟨fun ⟨y, hy⟩ ↦ ⟨e y, ?_⟩, fun ⟨y, hy⟩ ↦ ⟨e.symm y, e.injective ?_⟩⟩
      · rw [smul_eq_mul, ← map_pow, ← map_mul, ← smul_eq_mul, hy]
      · rw [smul_eq_mul, map_mul, map_pow, e.apply_symm_apply, ← smul_eq_mul, hy]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (fun n ↦ e.symm (f n))
      fun {m n} h ↦ (key _ _ m).2 (by simpa using hf h)
    exact ⟨e L, fun n ↦ by simpa using (key _ _ n).1 (hL n)⟩
