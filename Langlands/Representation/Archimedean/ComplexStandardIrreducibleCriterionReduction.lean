import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwap
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof

/-!
# Reduction of the irreducibility criterion ("if" part) for `GL_n(ℂ)`

`ComplexStandardIrreducibleCriterionStatement` (Sp_C, module `ComplexLargeStandardIrreducibleSplit`)
says that a Langlands-ordered complex standard module with no linked pair of characters is
irreducible. As in the real case (`RealStandardIrreducibleCriterionReduction`), this file reduces
it to the unlinked swap statement `ComplexStandardUnlinkedSwapStatement` (published) and one new
statement:

* `ComplexReverseIntertwinerKernelStatement`: every `(𝔤, K)`-intertwiner from a Langlands-ordered
  standard module to the standard module of the reversed list vanishes on every proper
  `(𝔤, K)`-submodule (a consequence of Langlands' theorem).

`complexStandardIrreducibleCriterionReduction` proves the implication: composing swaps gives an
injective intertwiner from the standard module of `ds` to that of `ds.reverse`, whose kernel
contains every proper `(𝔤, K)`-submodule.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

/-- **Intertwiners to the reversed standard module.** For a list `ds` of `n` complex characters
in Langlands order, every `(𝔤, K)`-intertwiner `T` from the `U(n)`-finite functions of the
standard module of `ds` to those of the standard module of `ds.reverse` vanishes on every proper
`(𝔤, K)`-submodule `W`. (By Langlands' theorem the image of a nonzero such `T` is the unique
irreducible submodule of the target, isomorphic to the Langlands quotient, which occurs with
multiplicity one; so `ker T` is the largest proper submodule.) -/
def ComplexReverseIntertwinerKernelStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData)
    (T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n ds.reverse) (unitaryCompact ℂ n))
    (W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))),
    ds.length = n → IsComplexLanglandsOrdered ds →
      IsComplexStandardIntertwining n (complexStandardRep n ds.reverse)
        (complexStandardLie n ds.reverse) ds T →
        IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W → W ≠ ⊤ →
          W ≤ LinearMap.ker T

/-- Unlinked swaps and intertwiners to the reversed module imply the "if" part of the
irreducibility criterion. -/
def ComplexStandardIrreducibleCriterionReductionStatement : Prop :=
  ComplexStandardUnlinkedSwapStatement → ComplexReverseIntertwinerKernelStatement →
    ComplexStandardIrreducibleCriterionStatement

/-! ## Composing intertwiners between standard modules -/

/-- There is an injective `(𝔤, K)`-intertwiner from the `U(n)`-finite functions of the
standard module of `ds` to those of the standard module of `es`. -/
def ComplexInjectiveIntertwinerExists (n : ℕ) (ds es : List ComplexCharacterData) : Prop :=
  ∃ T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n es) (unitaryCompact ℂ n),
    Function.Injective T ∧
      IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es) ds T

theorem ComplexInjectiveIntertwinerExists.refl (n : ℕ) (ds : List ComplexCharacterData) :
    ComplexInjectiveIntertwinerExists n ds ds :=
  ⟨LinearMap.id, Function.injective_id, isComplexStandardIntertwining_id n ds⟩

theorem ComplexInjectiveIntertwinerExists.trans {n : ℕ} {ds es fs : List ComplexCharacterData}
    (h₁ : ComplexInjectiveIntertwinerExists n ds es)
    (h₂ : ComplexInjectiveIntertwinerExists n es fs) :
    ComplexInjectiveIntertwinerExists n ds fs := by
  obtain ⟨T₁, hi₁, h₁⟩ := h₁
  obtain ⟨T₂, hi₂, h₂⟩ := h₂
  exact ⟨T₂ ∘ₗ T₁, hi₂.comp hi₁,
    h₁.comp T₂ (fun k v => h₂.map_complexStandardRep k v)
      (fun X v => h₂.map_complexStandardLie _ v)⟩

/-! ## Reversing a list by unlinked swaps -/

theorem isComplexLinked_comm {d e : ComplexCharacterData} :
    IsComplexLinked d e ↔ IsComplexLinked e d := by
  constructor <;>
  · rintro ⟨p, q, hpq, h1, h2⟩
    refine ⟨-p, -q, by rw [neg_mul_neg]; exact hpq, ?_, ?_⟩
    · push_cast; rw [← h1]; ring
    · push_cast; rw [← h2]; ring

/-- Moving a character `a` past a list `l` of characters all unlinked from `a`, one swap at a
time. -/
theorem complexInjectiveIntertwinerExists_moveToEnd (hSw : ComplexStandardUnlinkedSwapStatement)
    (n : ℕ) (a : ComplexCharacterData) :
    ∀ (l pre post : List ComplexCharacterData), (pre ++ a :: l ++ post).length = n →
      (∀ b ∈ l, ¬ IsComplexLinked a b) →
        ComplexInjectiveIntertwinerExists n (pre ++ a :: l ++ post) (pre ++ l ++ a :: post)
  | [], pre, post, _, _ => by
    simpa using ComplexInjectiveIntertwinerExists.refl n (pre ++ a :: post)
  | b :: l, pre, post, hlen, hl => by
    have hb := hl b List.mem_cons_self
    have e1 : pre ++ a :: (b :: l) ++ post = pre ++ a :: b :: (l ++ post) := by simp
    have e2 : pre ++ [b] ++ a :: l ++ post = pre ++ b :: a :: (l ++ post) := by simp
    have e3 : pre ++ [b] ++ l ++ a :: post = pre ++ (b :: l) ++ a :: post := by simp
    rw [e1] at hlen ⊢
    have hlen₂ : (pre ++ b :: a :: (l ++ post)).length = n := by
      rw [← hlen]; simp
    have h1 : ComplexInjectiveIntertwinerExists n (pre ++ a :: b :: (l ++ post))
        (pre ++ b :: a :: (l ++ post)) := by
      obtain ⟨T, hT, hTi⟩ := hSw n pre (l ++ post) b a hlen₂
        (fun h => hb (isComplexLinked_comm.mp h))
      exact ⟨T, hT.1, hTi⟩
    have hlen' : (pre ++ [b] ++ a :: l ++ post).length = n := by
      rw [e2, hlen₂]
    have h2 := complexInjectiveIntertwinerExists_moveToEnd hSw n a l (pre ++ [b]) post hlen'
      (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    rw [e2, e3] at h2
    exact h1.trans h2

/-- Reversing a pairwise unlinked list `l` by adjacent swaps, inside arbitrary lists `pre` and
`post`. -/
theorem complexInjectiveIntertwinerExists_reverse (hSw : ComplexStandardUnlinkedSwapStatement)
    (n : ℕ) :
    ∀ (l pre post : List ComplexCharacterData), (pre ++ l ++ post).length = n →
      l.Pairwise (fun a b => ¬ IsComplexLinked a b) →
        ComplexInjectiveIntertwinerExists n (pre ++ l ++ post) (pre ++ l.reverse ++ post)
  | [], pre, post, _, _ => by
    simpa using ComplexInjectiveIntertwinerExists.refl n (pre ++ post)
  | a :: l, pre, post, hlen, hl => by
    rw [List.pairwise_cons] at hl
    have h1 := complexInjectiveIntertwinerExists_moveToEnd hSw n a l pre post hlen hl.1
    have hlen' : (pre ++ l ++ a :: post).length = n := by
      rw [← hlen]; simp; omega
    have h2 := complexInjectiveIntertwinerExists_reverse hSw n l pre (a :: post) hlen' hl.2
    have e : pre ++ (a :: l).reverse ++ post = pre ++ l.reverse ++ a :: post := by simp
    rw [e]
    exact h1.trans h2

/-! ## The reduction -/

/-- **The reduction.** The standard module of `ds` is nonzero (`complexStandardNontrivial`).
Reversing `ds` by unlinked swaps gives an injective intertwiner `T` to the standard module of
`ds.reverse`. Every proper `(𝔤, K)`-submodule lies in `ker T = 0`. -/
theorem complexStandardIrreducibleCriterionReduction :
    ComplexStandardIrreducibleCriterionReductionStatement := by
  intro hSw hRev n ds hlen hord hu
  obtain ⟨T, hTinj, hT⟩ : ComplexInjectiveIntertwinerExists n ds ds.reverse := by
    simpa using complexInjectiveIntertwinerExists_reverse hSw n ds [] [] (by simpa using hlen) hu
  refine ⟨complexStandardNontrivial n ds hlen, fun W hWK hWX => ?_⟩
  by_cases hW : W = ⊤
  · exact Or.inr hW
  · left
    have hker := hRev n ds T W hlen hord hT ⟨hWK, hWX⟩ hW
    rw [LinearMap.ker_eq_bot.2 hTinj] at hker
    exact eq_bot_iff.2 hker

end Langlands.Archimedean
