import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.Ideal.Operations
import Langlands.ClassFieldTheory.Local.PrimeOrbitProductTraceExpansionStatement

/-! Proof of the prime-order orbit product expansion with an ideal-square trace witness. -/

namespace Langlands.LocalClassField

universe u v

open Finset
open scoped Pointwise

namespace PrimeOrbitProductTraceExpansionProof

/-- Sums over a finite invariant set of free orbits are orbit sums. Let a finite group act on
`β` and distributively on an additive monoid `M`, let `F : β → M` be equivariant, and let `s`
be an invariant finite set on which every orbit map `g ↦ g • b` is injective. If `F` takes
values in an additive submonoid `P` on `s`, then `∑ b ∈ s, F b = ∑ g, g • z` for some `z ∈ P`;
`z` is the sum of `F` over one representative of each orbit. -/
theorem exists_mem_sum_eq_sum_smul {G : Type*} [Group G] [Fintype G] {β : Type*}
    [MulAction G β] [DecidableEq β] {M : Type*} [AddCommMonoid M] [DistribMulAction G M]
    (F : β → M) (hF : ∀ (g : G) (b : β), F (g • b) = g • F b) (P : AddSubmonoid M)
    (s : Finset β) (hs : ∀ (g : G) (b : β), b ∈ s → g • b ∈ s)
    (hfree : ∀ b ∈ s, ∀ g h : G, g • b = h • b → g = h) (hP : ∀ b ∈ s, F b ∈ P) :
    ∃ z ∈ P, ∑ b ∈ s, F b = ∑ g : G, g • z := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · exact ⟨0, P.zero_mem, by simp⟩
    -- The orbit of `b`, a subset of `s`.
    set O : Finset β := (univ : Finset G).image (· • b) with hO
    have hOs : O ⊆ s := by
      intro c hc
      obtain ⟨g, -, rfl⟩ := mem_image.mp hc
      exact hs g b hb
    have hbO : b ∈ O := mem_image.mpr ⟨1, mem_univ _, one_smul G b⟩
    -- The complement of the orbit is again invariant.
    have hs' : ∀ (g : G) (c : β), c ∈ s \ O → g • c ∈ s \ O := by
      intro g c hc
      rw [mem_sdiff] at hc ⊢
      refine ⟨hs g c hc.1, fun hgc => hc.2 ?_⟩
      obtain ⟨h, -, hh⟩ := mem_image.mp hgc
      refine mem_image.mpr ⟨g⁻¹ * h, mem_univ _, ?_⟩
      rw [mul_smul, hh, inv_smul_smul]
    obtain ⟨z, hzP, hz⟩ := ih (s \ O) (sdiff_ssubset hOs ⟨b, hbO⟩) hs'
      (fun c hc => hfree c (mem_sdiff.mp hc).1) (fun c hc => hP c (mem_sdiff.mp hc).1)
    refine ⟨F b + z, P.add_mem (hP b hb) hzP, ?_⟩
    have horbit : ∑ c ∈ O, F c = ∑ g : G, g • F b := by
      rw [hO, sum_image (fun g _ h _ hgh => hfree b hb g h hgh)]
      exact sum_congr rfl fun g _ => hF g b
    rw [← sum_sdiff hOs, hz, horbit, ← sum_add_distrib]
    exact sum_congr rfl fun g _ => by rw [smul_add, add_comm]

/-- In a group of prime order, left translation acts freely on the subsets that are neither
empty nor the whole group. -/
theorem smul_finset_injective_of_prime_card {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (hp : (Fintype.card G).Prime) (S : Finset G) (hS0 : 0 < S.card)
    (hSp : S.card < Fintype.card G) (g h : G) (hgh : g • S = h • S) : g = h := by
  have : Fact (Nat.card G).Prime := ⟨by rwa [Nat.card_eq_fintype_card]⟩
  have hmem : h⁻¹ * g ∈ MulAction.stabilizer G S := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hgh, inv_smul_smul]
  rcases (MulAction.stabilizer G S).eq_bot_or_eq_top_of_prime_card with hbot | htop
  · rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  · -- Otherwise every translate of `S` equals `S`, so the nonempty set `S` is everything.
    exfalso
    obtain ⟨a, ha⟩ := card_pos.mp hS0
    have huniv : S = univ := by
      refine eq_univ_of_forall fun t => ?_
      have hfix : (t * a⁻¹) • S = S :=
        MulAction.mem_stabilizer_iff.mp (htop ▸ Subgroup.mem_top (t * a⁻¹))
      rw [← hfix]
      exact mem_smul_finset.mpr ⟨a, ha, by rw [smul_eq_mul, inv_mul_cancel_right]⟩
    rw [huniv, card_univ] at hSp
    exact lt_irrefl _ hSp

/-- A product of conjugates of an element of an invariant ideal, over a subset with at least
two elements, lies in the square of the ideal. -/
theorem prod_smul_mem_sq {G : Type*} [Group G] {R : Type*} [CommRing R]
    [MulSemiringAction G R] [DecidableEq G] (I : Ideal R)
    (hI : ∀ (g : G) (y : R), y ∈ I → g • y ∈ I) {x : R} (hx : x ∈ I) (S : Finset G)
    (hS : 2 ≤ S.card) : ∏ g ∈ S, g • x ∈ I ^ 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hS
  have hb' : b ∈ S.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
  rw [← mul_prod_erase S _ ha, ← mul_prod_erase (S.erase a) _ hb', ← mul_assoc, sq]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (hI a x hx) (hI b x hx))

/-- The product of conjugates over a translated subset is the conjugate of the product. -/
theorem prod_smul_smul_finset {G : Type*} [Group G] {R : Type*} [CommRing R]
    [MulSemiringAction G R] [DecidableEq G] (x : R) (k : G) (S : Finset G) :
    ∏ g ∈ k • S, g • x = k • ∏ g ∈ S, g • x := by
  rw [smul_finset_def, prod_image (fun g _ h _ hgh => MulAction.injective k hgh), smul_prod']
  exact prod_congr rfl fun g _ => mul_smul k g x

end PrimeOrbitProductTraceExpansionProof

open PrimeOrbitProductTraceExpansionProof in
/-- The prime-order orbit product expansion: the product of the conjugates of `1 + x` differs
from `1 + ∑ g, g • x + ∏ g, g • x` by the orbit sum of an element of `I ^ 2`. -/
theorem primeOrbitProductTraceExpansion : PrimeOrbitProductTraceExpansion.{u, v} := by
  intro G _ _ R _ _ hp I hI x hx
  classical
  -- The subsets with between `2` and `card G - 1` elements.
  let mid : Finset G → Prop := fun S => 2 ≤ S.card ∧ S.card < Fintype.card G
  obtain ⟨z, hzI, hz⟩ := exists_mem_sum_eq_sum_smul (G := G) (fun S => ∏ g ∈ S, g • x)
    (fun k S => prod_smul_smul_finset x k S) (I ^ 2).toAddSubmonoid (univ.filter mid)
    (fun k S hS => by
      simp only [mid, mem_filter, mem_univ, true_and, card_smul_finset] at hS ⊢
      exact hS)
    (fun S hS => by
      rw [mem_filter] at hS
      exact smul_finset_injective_of_prime_card hp S (by omega) hS.2.2)
    (fun S hS => prod_smul_mem_sq I hI hx S (mem_filter.mp hS).2.1)
  refine ⟨z, hzI, ?_⟩
  rw [← hz, prod_one_add, powerset_univ, ← sum_filter_add_sum_filter_not univ mid]
  -- The remaining subsets are the empty set, the singletons and the whole group.
  have hrest : univ.filter (fun S => ¬ mid S) =
      insert ∅ (insert univ ((univ : Finset G).image singleton)) := by
    ext S
    simp only [mid, mem_filter, mem_univ, true_and, mem_insert, mem_image, not_and, not_lt]
    constructor
    · intro hS
      by_cases h2 : 2 ≤ S.card
      · exact Or.inr (Or.inl (eq_univ_of_card S (le_antisymm (card_le_univ S) (hS h2))))
      · rcases (by omega : S.card = 0 ∨ S.card = 1) with hc | hc
        · exact Or.inl (card_eq_zero.mp hc)
        · obtain ⟨a, rfl⟩ := card_eq_one.mp hc
          exact Or.inr (Or.inr ⟨a, rfl⟩)
    · rintro (rfl | rfl | ⟨a, rfl⟩) h2
      · simp at h2
      · rw [card_univ]
      · simp at h2
  have hp2 := hp.two_le
  have huniv_ne : ∀ a : G, ({a} : Finset G) ≠ univ := fun a ha => by
    have := congrArg card ha
    rw [card_singleton, card_univ] at this
    omega
  have h0 : (∅ : Finset G) ∉ insert univ ((univ : Finset G).image singleton) := by
    simp only [mem_insert, mem_image, mem_univ, true_and, not_or, not_exists]
    exact ⟨(univ_nonempty (α := G)).ne_empty.symm, fun a => singleton_ne_empty a⟩
  have h1 : (univ : Finset G) ∉ (univ : Finset G).image singleton := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact huniv_ne
  rw [hrest, sum_insert h0, sum_insert h1, sum_image (fun a _ b _ hab => singleton_injective hab)]
  simp only [prod_empty, prod_singleton]
  abel
