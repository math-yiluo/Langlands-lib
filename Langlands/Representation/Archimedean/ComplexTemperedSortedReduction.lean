import Langlands.Representation.Archimedean.ComplexTemperedIrreducibleStatement
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction
import Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducibleProof
import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction

/-!
# Reduction of tempered irreducibility to lists sorted by weight

`ComplexTemperedSortedReductionStatement`: if the standard module of every list of `n` complex
characters whose exponents have equal real parts and whose weights do not decrease along the
list is irreducible, then `ComplexTemperedStandardIrreducibleStatement` holds. The theorem
`complexTemperedSortedReduction` proves it. Characters with exponents of equal real part are
not linked (`not_linked_of_re_eq`), and the standard module of a list of pairwise unlinked
characters is irreducible as soon as the standard module of one of its permutations is
(`complexStandardIrreducible_of_perm`), by adjacent swaps (`complexStandardUnlinkedSwapReduction`
with `complexGLTwoUnlinkedIrreducible`). See the Markdown file.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

-- As in `ComplexLargeStandardIrreducibleSplit`: the charts on units need reduction through the
-- normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace ComplexTemperedSorted

/-- Linkage is symmetric. -/
theorem not_linked_symm {d e : ComplexCharacterData} (h : ¬ IsComplexLinked d e) :
    ¬ IsComplexLinked e d := by
  rintro ⟨a, b, hab, h1, h2⟩
  refine h ⟨-a, -b, by rw [neg_mul_neg]; exact hab, ?_, ?_⟩
  · push_cast
    rw [← h1]
    ring
  · push_cast
    rw [← h2]
    ring

/-- Two characters whose exponents have the same real part are not linked: the two integers
`p`, `q` of a linkage add up to twice the difference of the exponents, which is purely
imaginary, so `q = -p` and `p q ≤ 0`. -/
theorem not_linked_of_re_eq {d e : ComplexCharacterData} (h : d.exponent.re = e.exponent.re) :
    ¬ IsComplexLinked d e := by
  rintro ⟨p, q, hpq, h1, h2⟩
  have hsum : ((p + q : ℤ) : ℂ) = 2 * (d.exponent - e.exponent) := by
    push_cast
    rw [← h1, ← h2]
    ring
  have hre : ((p + q : ℤ) : ℝ) = 0 := by
    have := congrArg Complex.re hsum
    rw [Complex.intCast_re] at this
    rw [this]
    simp [h]
  have hpq0 : p + q = 0 := by exact_mod_cast hre
  have hq : q = -p := by omega
  subst hq
  nlinarith [mul_self_nonneg p]

/-- A list of characters whose exponents all have the same real part is pairwise unlinked. -/
theorem isComplexUnlinked_of_re_eq {ds : List ComplexCharacterData}
    (h : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) : IsComplexUnlinked ds :=
  List.pairwise_of_forall_mem_list fun d hd e he => not_linked_of_re_eq (h d hd e he)

/-- One adjacent swap: if `d`, `e` are not linked and the standard module of
`pre ++ d :: e :: post` is irreducible, so is the standard module of `pre ++ e :: d :: post`.
The swap statement gives a bijective intertwining map from the latter onto the former. -/
theorem irreducible_swap (hswap : ComplexStandardUnlinkedSwapStatement) (n : ℕ)
    (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
    (hn : (pre ++ d :: e :: post).length = n) (h : ¬ IsComplexLinked d e)
    (hirr : IsIrreducibleGKModule (complexStandardRep n (pre ++ d :: e :: post))
      (complexStandardLie n (pre ++ d :: e :: post))) :
    IsIrreducibleGKModule (complexStandardRep n (pre ++ e :: d :: post))
      (complexStandardLie n (pre ++ e :: d :: post)) := by
  obtain ⟨T, hbij, hT⟩ := hswap n pre post d e hn h
  have hnt : Nontrivial (kFiniteFunctions (complexStandardModule n (pre ++ e :: d :: post))
      (unitaryCompact ℂ n)) := by
    obtain ⟨x, y, hxy⟩ := hirr.1.exists_pair_ne
    obtain ⟨x', rfl⟩ := hbij.2 x
    obtain ⟨y', rfl⟩ := hbij.2 y
    exact ⟨⟨x', y', fun hx => hxy (by rw [hx])⟩⟩
  exact isIrreducibleGKModule_of_injective hirr hT hbij.1 hnt

/-- Permutations of a pairwise unlinked tail: for `l₁ ~ l₂` with `l₁` pairwise unlinked,
irreducibility of the standard module of `pre ++ l₁` implies that of `pre ++ l₂`. Induction
on the permutation. -/
theorem irreducible_of_perm_append (hswap : ComplexStandardUnlinkedSwapStatement) :
    ∀ {l₁ l₂ : List ComplexCharacterData}, l₁.Perm l₂ → ∀ (n : ℕ) (pre : List ComplexCharacterData),
      (pre ++ l₁).length = n → IsComplexUnlinked l₁ →
      IsIrreducibleGKModule (complexStandardRep n (pre ++ l₁)) (complexStandardLie n (pre ++ l₁)) →
      IsIrreducibleGKModule (complexStandardRep n (pre ++ l₂)) (complexStandardLie n (pre ++ l₂)) := by
  intro l₁ l₂ hp
  induction hp with
  | nil => exact fun _ _ _ _ h => h
  | @cons x l₁ l₂ _ ih =>
    intro n pre hn hu hirr
    rw [List.append_cons] at hn hirr ⊢
    exact ih n (pre ++ [x]) hn (List.pairwise_cons.1 hu).2 hirr
  | swap x y l =>
    intro n pre hn hu hirr
    have hyx : ¬ IsComplexLinked y x := (List.pairwise_cons.1 hu).1 x (by simp)
    exact irreducible_swap hswap n pre l y x hn hyx hirr
  | @trans l₁ l₂ l₃ h₁ _ ih₁ ih₂ =>
    intro n pre hn hu hirr
    have hn₂ : (pre ++ l₂).length = n := by
      rw [List.length_append, ← h₁.length_eq, ← List.length_append]
      exact hn
    exact ih₂ n pre hn₂ (h₁.pairwise hu not_linked_symm) (ih₁ n pre hn hu hirr)

end ComplexTemperedSorted

open ComplexTemperedSorted

/-- **Irreducibility is invariant under permuting unlinked characters.** If `ds` is a list of
`n` pairwise unlinked complex characters, `ds'` is a permutation of `ds`, and the standard module
of `ds'` is irreducible, then so is the standard module of `ds`. -/
theorem complexStandardIrreducible_of_perm (n : ℕ) (ds ds' : List ComplexCharacterData)
    (hlen : ds'.length = n) (hperm : ds'.Perm ds) (hunl : IsComplexUnlinked ds')
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds') (complexStandardLie n ds')) :
    IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) :=
  irreducible_of_perm_append (complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible)
    hperm n [] hlen hunl hirr

/-- **Reduction of tempered irreducibility to weight-sorted lists.** If the standard module of
every list of `n` complex characters whose exponents have the same real part and whose weights
do not decrease along the list is irreducible, then the standard module of every list of
complex characters whose exponents have the same real part is irreducible. -/
def ComplexTemperedSortedReductionStatement : Prop :=
  (∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
      (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
      ds.Pairwise (fun d e => d.weight ≤ e.weight) →
      IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)) →
    ComplexTemperedStandardIrreducibleStatement

/-- Proof of the reduction: sort `ds` by weight (`List.mergeSort`), apply the hypothesis to the
sorted list, and go back with `complexStandardIrreducible_of_perm`. -/
theorem complexTemperedSortedReduction : ComplexTemperedSortedReductionStatement := by
  intro hsorted n ds hlen htemp
  set ds' := ds.mergeSort (fun d e => decide (d.weight ≤ e.weight)) with hds'
  have hperm : ds'.Perm ds := List.mergeSort_perm _ _
  have hmem : ∀ d, d ∈ ds' ↔ d ∈ ds := fun d => hperm.mem_iff
  have htemp' : ∀ d ∈ ds', ∀ e ∈ ds', d.exponent.re = e.exponent.re :=
    fun d hd e he => htemp d ((hmem d).1 hd) e ((hmem e).1 he)
  have hlen' : ds'.length = n := hperm.length_eq.trans hlen
  have hsort : ds'.Pairwise (fun d e => d.weight ≤ e.weight) := by
    have := List.pairwise_mergeSort (le := fun d e : ComplexCharacterData =>
        decide (d.weight ≤ e.weight))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact hab.trans hbc)
      (fun a b => by
        rcases le_total a.weight b.weight with h | h
        · simp [h]
        · simp [h])
      ds
    exact this.imp fun h => by simpa using h
  exact complexStandardIrreducible_of_perm n ds ds' hlen' hperm (isComplexUnlinked_of_re_eq htemp')
    (hsorted n ds' hlen' htemp' hsort)

end Langlands.Archimedean
