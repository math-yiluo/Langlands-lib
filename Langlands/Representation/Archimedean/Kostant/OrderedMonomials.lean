import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Langlands.Representation.Archimedean.Kostant.Symbol

/-!
# Ordered monomials in the universal enveloping algebra

Fix a basis `b` of a Lie algebra `L`, indexed by a finite type `B`, and a list `bs` enumerating
`B` without repetition. For an exponent vector `α : B →₀ ℕ` the ordered monomial `E^α` is the
product of the generators `b c`, `c` running through `bs` in order, each repeated `α c` times.

* `degreeFiltration_le_span_orderedMonomial`: the filtration piece `U_N` is spanned by the
  ordered monomials of degree at most `N` (the spanning half of the Poincaré–Birkhoff–Witt
  theorem): a word is a sum of words in basis elements, and reordering a word changes it only by
  an element of lower degree.
* `mem_degreeFiltration_of_symbol_eq_zero`: if the symbols of `SymbolData` send `b c` to the
  variable `X c` of `MvPolynomial B K`, then an element of `U_{N+1}` with vanishing degree-`(N+1)`
  symbol lies in `U_N`, because the symbols of the ordered monomials of degree `N + 1` are the
  distinct monomials `X^α`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping MvPolynomial

section Expand

variable {B : Type*} [DecidableEq B]

/-- The list of the indices of `bs`, each `c` repeated `α c` times. -/
def expand (bs : List B) (α : B →₀ ℕ) : List B :=
  bs.flatMap fun c => List.replicate (α c) c

variable [Fintype B] {bs : List B}

theorem count_expand (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (α : B →₀ ℕ) (a : B) :
    (expand bs α).count a = α a := by
  unfold expand
  rw [List.count_flatMap]
  have h : (bs.map ((List.count a) ∘ fun c => List.replicate (α c) c)).sum =
      ∑ c ∈ bs.toFinset, ((List.count a) ∘ fun c => List.replicate (α c) c) c :=
    (List.sum_toFinset _ hbs).symm
  rw [h, show bs.toFinset = Finset.univ from
    Finset.eq_univ_iff_forall.mpr fun c => List.mem_toFinset.mpr (hall c)]
  simp only [Function.comp_apply, List.count_replicate, beq_iff_eq]
  rw [Finset.sum_ite_eq' Finset.univ a fun c => α c]
  simp

theorem coe_expand (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (α : B →₀ ℕ) :
    ((expand bs α : List B) : Multiset B) = Finsupp.toMultiset α := by
  ext a
  rw [Multiset.coe_count, count_expand hbs hall, Finsupp.count_toMultiset]

theorem length_expand (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (α : B →₀ ℕ) :
    (expand bs α).length = α.degree := by
  rw [← Multiset.coe_card, coe_expand hbs hall, Finsupp.card_toMultiset]
  rfl

theorem perm_expand (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (cs : List B) :
    cs.Perm (expand bs (Multiset.toFinsupp (cs : Multiset B))) := by
  rw [← Multiset.coe_eq_coe, coe_expand hbs hall, Multiset.toFinsupp_toMultiset]

omit [Fintype B] in
theorem degree_toFinsupp (cs : List B) :
    (Multiset.toFinsupp (cs : Multiset B)).degree = cs.length := by
  have h := Finsupp.card_toMultiset (Multiset.toFinsupp (cs : Multiset B))
  rw [Multiset.toFinsupp_toMultiset, Multiset.coe_card] at h
  rw [h]
  rfl

end Expand

section Monomials

variable (K : Type*) [Field K] (L : Type*) [LieRing L] [LieAlgebra K L]
  {B : Type*} [Fintype B] [DecidableEq B] (b : Module.Basis B K L) (bs : List B)

local notation "U" => UniversalEnvelopingAlgebra K L

/-- The ordered monomial `E^α`. -/
def orderedMonomial (α : B →₀ ℕ) : U := word K L ((expand bs α).map b)

/-- The span of the ordered monomials of degree at most `N`. -/
def orderedSpan (N : ℕ) : Submodule K U :=
  Submodule.span K (orderedMonomial K L b bs '' {α | α.degree ≤ N})

omit [Fintype B] [DecidableEq B] in
theorem orderedSpan_mono {M N : ℕ} (h : M ≤ N) :
    orderedSpan K L b bs M ≤ orderedSpan K L b bs N :=
  Submodule.span_mono (Set.image_mono fun _ (hα : _ ≤ M) => hα.trans h)

variable {bs}

theorem orderedMonomial_mem_degreeFiltration (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs)
    (α : B →₀ ℕ) : orderedMonomial K L b bs α ∈ degreeFiltration K L α.degree := by
  have h := word_mem_degreeFiltration K L ((expand bs α).map b)
  rwa [List.length_map, length_expand hbs hall] at h

theorem orderedSpan_le_degreeFiltration (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (N : ℕ) :
    orderedSpan K L b bs N ≤ degreeFiltration K L N := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨α, hα, rfl⟩
  exact degreeFiltration_mono K L hα (orderedMonomial_mem_degreeFiltration K L b hbs hall α)

omit [DecidableEq B] in
/-- A word is a combination of words in basis elements of the same length. -/
theorem word_mem_span_basisWords (l : List L) :
    word K L l ∈ Submodule.span K
      {u | ∃ cs : List B, cs.length = l.length ∧ word K L (cs.map b) = u} := by
  induction l with
  | nil => exact Submodule.subset_span ⟨[], rfl, rfl⟩
  | cons x l ih =>
    rw [word_cons]
    have hx : UniversalEnvelopingAlgebra.ι K x =
        ∑ c, b.repr x c • UniversalEnvelopingAlgebra.ι K (b c) := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      simp only [map_smul]
    rw [hx, Finset.sum_mul]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    have key : ∀ u ∈ Submodule.span K
        {u | ∃ cs : List B, cs.length = l.length ∧ word K L (cs.map b) = u},
        UniversalEnvelopingAlgebra.ι K (b c) * u ∈ Submodule.span K
          {u | ∃ cs : List B, cs.length = (x :: l).length ∧ word K L (cs.map b) = u} := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨cs, hcs, rfl⟩ := hu
        refine Submodule.subset_span ⟨c :: cs, by simp [hcs], ?_⟩
        simp [word_cons]
      | zero => simp
      | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
      | smul a u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hu
    exact key _ ih

/-- `U_N` is spanned by the ordered monomials of degree at most `N`. -/
theorem degreeFiltration_le_orderedSpan (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (N : ℕ) :
    degreeFiltration K L N ≤ orderedSpan K L b bs N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hbasic : ∀ cs : List B, cs.length ≤ N →
        word K L (cs.map b) ∈ orderedSpan K L b bs N := by
      intro cs hcs
      set α := Multiset.toFinsupp (cs : Multiset B)
      have hα : α.degree = cs.length := degree_toFinsupp cs
      have hmon : orderedMonomial K L b bs α ∈ orderedSpan K L b bs N :=
        Submodule.subset_span ⟨α, show α.degree ≤ N by omega, rfl⟩
      rcases Nat.eq_zero_or_pos cs.length with h0 | hpos
      · have : cs = [] := List.length_eq_zero_iff.mp h0
        subst this
        have he : expand bs α = [] := List.flatMap_eq_nil_iff.mpr (by simp [α])
        simpa [orderedMonomial, he] using hmon
      · have hperm := ((perm_expand hbs hall cs).map b)
        have hdiff := word_sub_word_mem_of_perm K L hperm
        rw [List.length_map] at hdiff
        have hlow : word K L (cs.map b) - orderedMonomial K L b bs α ∈
            orderedSpan K L b bs N :=
          orderedSpan_mono K L b bs (by omega) (ih (cs.length - 1) (by omega) hdiff)
        simpa using Submodule.add_mem _ hlow hmon
    have hword : ∀ u ∈ Submodule.span K
        {u | ∃ cs : List B, cs.length ≤ N ∧ word K L (cs.map b) = u},
        u ∈ orderedSpan K L b bs N := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨cs, hcs, rfl⟩ := hv
        exact hbasic cs hcs
      | zero => exact Submodule.zero_mem _
      | add v w _ _ hv hw => exact Submodule.add_mem _ hv hw
      | smul a v _ hv => exact Submodule.smul_mem _ a hv
    intro P hP
    have hP' := degreeFiltration_le_wordSpan K L N hP
    clear hP
    induction hP' using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨l, hl, rfl⟩ := hu
      refine hword _ (Submodule.span_mono ?_ (word_mem_span_basisWords K L b l))
      rintro _ ⟨cs, hcs, rfl⟩
      exact ⟨cs, by omega, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add u v _ _ hu hv => exact Submodule.add_mem _ hu hv
    | smul a u _ hu => exact Submodule.smul_mem _ a hu

omit [Fintype B] in
theorem list_prod_map_X (cs : List B) :
    (cs.map fun c => (X c : MvPolynomial B K)).prod =
      monomial (Multiset.toFinsupp (cs : Multiset B)) 1 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons, ih, ← Multiset.cons_coe, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, X, monomial_mul_monomial, one_mul]

variable {R : Type*} [CommRing R] [Algebra K R]
variable [CharZero K]

theorem symbol_orderedMonomial (d : SymbolData K L R (MvPolynomial B K))
    (hξ : ∀ c, d.ξ (b c) = X c) (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) {α : B →₀ ℕ} {N : ℕ}
    (hα : α.degree ≤ N) :
    d.symbol N (orderedMonomial K L b bs α) = if α.degree = N then monomial α 1 else 0 := by
  unfold orderedMonomial
  split_ifs with h
  · rw [d.symbol_word_of_length_eq _ (by rw [List.length_map, length_expand hbs hall, h]),
      List.map_map]
    have : (d.ξ ∘ b) = fun c => (X c : MvPolynomial B K) := funext hξ
    rw [this, list_prod_map_X, Multiset.toFinsupp_eq_iff.mpr (coe_expand hbs hall α)]
  · exact d.symbol_word_of_length_lt _ (by rw [List.length_map, length_expand hbs hall]; omega)

/-- An element of `U_{N+1}` whose degree-`(N+1)` symbol vanishes lies in `U_N`. -/
theorem mem_degreeFiltration_of_symbol_eq_zero (d : SymbolData K L R (MvPolynomial B K))
    (hξ : ∀ c, d.ξ (b c) = X c) (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) {N : ℕ} {P : U}
    (hP : P ∈ degreeFiltration K L (N + 1)) (h0 : d.symbol (N + 1) P = 0) :
    P ∈ degreeFiltration K L N := by
  have hP' := degreeFiltration_le_orderedSpan K L b hbs hall (N + 1) hP
  obtain ⟨c, hc, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hP'
  have hsupp : ∀ α ∈ c.support, α.degree ≤ N := by
    intro α hα
    have hαN : α.degree ≤ N + 1 := hc hα
    by_contra hlt
    have heq : α.degree = N + 1 := by omega
    have hcoeff := congrArg (lcoeff K α) h0
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_zero, map_sum, map_sum,
      Finset.sum_eq_single α] at hcoeff
    · rw [map_smul, map_smul, symbol_orderedMonomial K L b d hξ hbs hall hαN, ite_eq_left heq,
        lcoeff_apply, coeff_monomial, ite_eq_left rfl, smul_eq_mul, mul_one] at hcoeff
      exact (Finsupp.mem_support_iff.mp hα) hcoeff
    · intro β hβ hβα
      rw [map_smul, map_smul, symbol_orderedMonomial K L b d hξ hbs hall (hc hβ)]
      split_ifs
      · rw [lcoeff_apply, coeff_monomial, ite_eq_right hβα, smul_zero]
      · simp
    · intro h; exact absurd hα h
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
  exact degreeFiltration_mono K L (hsupp α hα)
    (orderedMonomial_mem_degreeFiltration K L b hbs hall α)

end Monomials

end Langlands.Archimedean.Kostant
