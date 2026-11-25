/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.FieldTheory.ExistsPBasis
import WeilConjectures.FieldTheory.IntersectionSubfieldsSubspace
import WeilConjectures.FieldTheory.PBasisDifferentialsBasis
import WeilConjectures.FieldTheory.PIndependentDifferentialsIndependent

/-! # Differential kernel detection

Source: Stacks Project, More on Algebra, Tag 07P4.
(blueprint: lem-weil-pbc-intersection-subfields-differentials-kernel)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v
namespace FieldTheory
local instance zmodAlgebraKernel (p : ℕ) (K : Type u) [Field K] [CharP K p] :
    Algebra (ZMod p) K := ZMod.algebra (R := K) p

private theorem finite_independent_some_field
    {k : Type*} {L : Type*} [Field k] [Field L] [Algebra k L]
    {A : Type*} [Nonempty A] (F : A → IntermediateField k L)
    (hF : (⨅ a, F a) = ⊥)
    (hd : ∀ a b, ∃ c, F c ≤ F a ⊓ F b)
    (n : ℕ) (z : Fin n → L) (hz : LinearIndependent k z) :
    ∃ a, LinearIndependent (F a) z := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨Classical.arbitrary A, linearIndependent_empty_type⟩
  by_contra! h
  let V : Submodule L (Fin n → L) :=
    LinearMap.ker (Fintype.linearCombination L z)
  have hrel : ∀ a, ∃ x : Fin n → L,
      x ∈ V ∧ x ≠ 0 ∧ ∀ i, x i ∈ F a := by
    intro a
    have ha := h a
    rw [Fintype.linearIndependent_iff] at ha
    push Not at ha
    obtain ⟨c, hc, i, hi⟩ := ha
    refine ⟨fun j ↦ (c j : L), ?_, ?_, fun j ↦ (c j).property⟩
    · simpa [V, LinearMap.mem_ker, Fintype.linearCombination_apply,
        Algebra.smul_def] using hc
    · intro he
      apply hi
      apply Subtype.ext
      exact congrFun he i
  obtain ⟨x, hx, hne, hbase⟩ :=
    (IntermediateField.exists_ne_zero_mem_base_iff_forall_mem_intermediateField
      F hF hd n (Nat.one_le_iff_ne_zero.mpr hn) V).mpr hrel
  have hxbase : ∀ i, ∃ c : k, algebraMap k L c = x i := by
    intro i
    exact (IntermediateField.mem_bot.mp (hbase i))
  choose c hc using hxbase
  have hsum : ∑ i, c i • z i = 0 := by
    have hx' : ∑ i, x i * z i = 0 := by
      simpa [V, LinearMap.mem_ker, Fintype.linearCombination_apply, smul_eq_mul] using hx
    simpa [Algebra.smul_def, hc] using hx'
  have hc0 := (Fintype.linearIndependent_iff.mp hz) c hsum
  apply hne
  funext i
  simp only [Pi.zero_apply, ← hc i, hc0 i, map_zero]

private theorem finite_independent_some_field'
    {k : Type*} {L : Type*} [Field k] [Field L] [Algebra k L]
    {A : Type*} [Nonempty A] (F : A → IntermediateField k L)
    (hF : (⨅ a, F a) = ⊥)
    (hd : ∀ a b, ∃ c, F c ≤ F a ⊓ F b)
    {T : Type*} [Finite T] (z : T → L) (hz : LinearIndependent k z) :
    ∃ a, LinearIndependent (F a) z := by
  classical
  let := Fintype.ofFinite T
  let e := Fintype.equivFin T
  obtain ⟨a, ha⟩ := finite_independent_some_field F hF hd
    (Fintype.card T) (fun i ↦ z (e.symm i)) (hz.comp e.symm e.symm.injective)
  exact ⟨a, by simpa only [Function.comp_def, Equiv.symm_apply_apply] using
    (ha.comp e e.injective)⟩

private theorem independent_adjoin_of_subset
    {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]
    {T : Type*} (z : T → K) (hz : LinearIndependent k z)
    (S : Set K) (hS : S ⊆ (⊥ : IntermediateField k K)) :
    LinearIndependent (IntermediateField.adjoin k S) z := by
  have h : IntermediateField.adjoin k S = ⊥ :=
    le_antisymm (IntermediateField.adjoin_le_iff.mpr hS) bot_le
  rw [h]
  exact hz.restrict_scalars' (⊥ : IntermediateField k K)

/-- Differential kernel detection.
Source: Stacks Project, More on Algebra, Tag 07P4 (`lemma-intersection-subfields`),
`literature/stacks-project/more-algebra.tex`.
(blueprint: lem-weil-pbc-intersection-subfields-differentials-kernel)

Proof:

1. Frobenius is an injective ring homomorphism, so `K^p` and `L^p` are subfields, and the
prime field lies in `K^p`. Choose a p-basis `x_i` of `K` over the prime field using
`lem-weil-pbc-p-basis-exists`. Its p-monomials form a basis over `K^p`, and `dx_i` form a
basis of the absolute differentials by `lem-weil-pbc-p-basis-differentials-basis`.

2. If a nonzero differential dies in every relative module, express it with finite nonempty
support in the `dx_i`. By `lem-weil-pbc-p-independent-differentials-independent`, its
support's p-monomials have a nontrivial relation over each `Kα`. The space of relations
therefore meets every `Kα^N` nontrivially. The index family is nonempty: otherwise the
intersection condition makes `K` perfect, contradicting the nonempty p-basis support.
Apply `theorem-finite-etale-covers-proper-henselian--2` to obtain a nontrivial relation over
`K^p`, contradicting the p-basis monomials' independence. This proves the first clause. -/
theorem intersection_subfields_differentials_kernel
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    {ι : Type v} (Kα : ι → IntermediateField (ZMod p) K)
    (h₁ : ∀ α : ι, Set.range (fun x : K => x ^ p) ⊆ (Kα α : Set K))
    (h₂ : Set.range (fun x : K => x ^ p) =
      ((⨅ α, Kα α : IntermediateField (ZMod p) K) : Set K))
    (h₃ : ∀ α β : ι, ∃ γ : ι, Kα γ ≤ Kα α ⊓ Kα β) :
    ∀ ω : Ω[K⁄ZMod p],
      (∀ α : ι, KaehlerDifferential.map (ZMod p) (Kα α) K K ω = 0) → ω = 0 := by
  classical
  intro ω hω
  let f (α : ι) : Ω[K⁄ZMod p] →ₗ[K] Ω[K⁄Kα α] :=
    KaehlerDifferential.map (ZMod p) (Kα α) K K
  let B := IntermediateField.adjoin (ZMod p) (Set.range (fun x : K ↦ x ^ p))
  have hBα : ∀ α, B ≤ Kα α := fun α ↦ IntermediateField.adjoin_le_iff.mpr (h₁ α)
  have hBinf : B = ⨅ α, Kα α := by
    apply le_antisymm
    · exact le_iInf hBα
    · intro x hx
      apply IntermediateField.subset_adjoin
      rw [h₂]
      exact hx
  by_cases hι : Nonempty ι
  · have := hι
    let L : ι → IntermediateField B K := fun α ↦ IntermediateField.extendScalars (hBα α)
    have hLinf : (⨅ α, L α) = ⊥ := by
      apply SetLike.ext
      intro x
      change x ∈ ((⨅ α, L α : IntermediateField B K) : Set K) ↔ x ∈ (⊥ : IntermediateField B K)
      rw [IntermediateField.coe_iInf]
      simp only [Set.mem_iInter, IntermediateField.mem_bot]
      constructor
      · intro hx
        have hxB : x ∈ B := by
          rw [hBinf]
          change x ∈ ((⨅ α, Kα α : IntermediateField (ZMod p) K) : Set K)
          rw [IntermediateField.coe_iInf]
          exact Set.mem_iInter.mpr hx
        exact ⟨⟨x, hxB⟩, rfl⟩
      · rintro ⟨c, rfl⟩ α
        exact hBα α c.property
    have hLd : ∀ α β, ∃ γ, L γ ≤ L α ⊓ L β := by
      intro α β
      obtain ⟨γ, hγ⟩ := h₃ α β
      refine ⟨γ, le_inf ?_ ?_⟩
      · intro x hx
        exact (hγ hx).1
      · intro x hx
        exact (hγ hx).2
    obtain ⟨I, t, b, hb⟩ := Field.exists_p_basis p K
    obtain ⟨db, hdb⟩ := KaehlerDifferential.exists_basis_differentials_of_pBasis
      p t ⟨b, hb⟩
    let c := db.repr ω
    let T := {i // i ∈ c.support}
    let e : T ↪ I := Function.Embedding.subtype _
    let M := {E : T →₀ ℕ // ∀ i, E i < p}
    have hM : Finite M := by
      let f : M → (T → Fin p) := fun E i ↦ ⟨E.val i, E.property i⟩
      exact Finite.of_injective f (by
        intro E E' h
        apply Subtype.ext
        apply Finsupp.ext
        intro i
        exact congrArg Fin.val (congrFun h i))
    let := Fintype.ofFinite M
    let emb : M → {E : I →₀ ℕ // ∀ i, E i < p} := fun E ↦
      ⟨E.val.embDomain e, by
        intro i
        rw [Finsupp.embDomain_apply]
        split
        · exact E.property _
        · exact (Fact.out : p.Prime).pos⟩
    have hemb : Function.Injective emb := by
      intro E E' h
      apply Subtype.ext
      exact Finsupp.embDomain_injective e (congrArg Subtype.val h)
    let z : M → K := fun E ↦ E.val.prod (fun i n ↦ t (e i) ^ n)
    have hz : LinearIndependent B z := by
      have hh := b.linearIndependent.comp emb hemb
      simpa only [Function.comp_def, hb, emb, Finsupp.prod_embDomain] using hh
    obtain ⟨α, hα⟩ := finite_independent_some_field' L hLinf hLd z hz
    have hα' : LinearIndependent (Kα α) z := hα
    have hmon := independent_adjoin_of_subset z hα'
      (Set.range (fun x : K ↦ x ^ p)) (by
        rintro x ⟨y, rfl⟩
        exact IntermediateField.mem_bot.mpr ⟨⟨y ^ p, h₁ α ⟨y, rfl⟩⟩, rfl⟩)
    have : CharP (Kα α) p :=
      charP_of_injective_algebraMap (algebraMap (ZMod p) (Kα α)).injective p
    have hdiff := pIndependent_differentials_linearIndependent p (Kα α) K
      (fun i : T ↦ t (e i)) hmon
    have hsum : ∑ i : T, c i.val • KaehlerDifferential.D (Kα α) K (t i.val) = 0 := by
      have hrepr := db.linearCombination_repr ω
      have hmap := congrArg (f α) hrepr
      have hfω : f α ω = 0 := hω α
      rw [hfω] at hmap
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at hmap
      simp only [map_smul, hdb] at hmap
      dsimp only [f] at hmap
      simp only [KaehlerDifferential.map_D, Algebra.algebraMap_self,
        RingHom.id_apply] at hmap
      rw [← Finset.sum_attach] at hmap
      exact hmap
    have hc := (Fintype.linearIndependent_iff.mp hdiff) (fun i ↦ c i.val) hsum
    have hc0 : c = 0 := by
      apply Finsupp.ext
      intro i
      by_cases hi : i ∈ c.support
      · exact hc ⟨i, hi⟩
      · exact Finsupp.notMem_support_iff.mp hi
    exact db.repr.injective (by simpa [c] using hc0)
  · have he : IsEmpty ι := not_nonempty_iff.mp hι
    have := he
    have hpow : ∀ x : K, ∃ y : K, y ^ p = x := by
      intro x
      have hx : x ∈ ((⨅ α, Kα α : IntermediateField (ZMod p) K) : Set K) := by
        simp
      rw [← h₂] at hx
      exact hx
    have hD : ∀ x : K, KaehlerDifferential.D (ZMod p) K x = 0 := by
      intro x
      obtain ⟨y, rfl⟩ := hpow x
      rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero]
      simp
    have hz : (⊤ : Submodule K Ω[K⁄ZMod p]) ≤ ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation (ZMod p) K]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      simpa using hD x
    exact hz (Submodule.mem_top)
end FieldTheory
