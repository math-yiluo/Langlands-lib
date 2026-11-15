import Langlands.Representation.Archimedean.RealLargeStandardIrreducibleReduction

/-!
# Reduction of Speh's irreducibility criterion ("if" part) for `GL_n(ℝ)`

`RealStandardIrreducibleCriterionStatement` (module `RealLargeStandardIrreducibleReduction`)
says that a Langlands-ordered real standard module none of whose Mœglin data are linked is
irreducible. Following Mœglin (1997, §8, p. 163), this file reduces it to two statements
about standard modules, besides the Langlands-quotient statement
`RealStandardLanglandsQuotientStatement`:

* `RealUnlinkedSwapStatement`: exchanging two adjacent unlinked blocks, the first of which has
  the larger (or equal) real exponent, gives an injective `(𝔤, K)`-intertwiner between the
  two standard modules (Mœglin's normalized rank-one intertwining operator, §§7–8, and the
  reduction to `GL_2`, `GL_3`, `GL_4`, p. 165);
* `RealReverseIntertwinerKernelStatement`: every `(𝔤, K)`-intertwiner from a Langlands-ordered
  standard module to the standard module of the reversed list of blocks vanishes on every
  proper `(𝔤, K)`-submodule (a consequence of Langlands' theorem, Mœglin's Theorem 4).

`realStandardIrreducibleCriterionReduction` proves that the three statements imply
`RealStandardIrreducibleCriterionStatement`: composing swaps gives an injective intertwiner
from the standard module of `ds` to that of `ds.reverse`, whose kernel contains every proper
`(𝔤, K)`-submodule.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `RealLargeStandardIrreducibleReduction`.
set_option backward.isDefEq.respectTransparency false

/-! ## Unlinked blocks -/

/-- Two real blocks are unlinked when no Mœglin datum of the first is linked to a Mœglin datum
of the second (Mœglin 1997, Theorem 10b, for the pair of blocks). -/
def AreRealBlocksUnlinked (x y : RealBlock) : Prop :=
  ∀ a ∈ realBlockMoeglinData x, ∀ b ∈ realBlockMoeglinData y, ¬ a.IsLinked b

/-! ## The two statements -/

/-- **Unlinked adjacent swaps.** For lists `pre`, `post` and blocks `x`, `y` of total rank `n`
with `Re t(y) ≤ Re t(x)` whose Mœglin data are not linked, there is an injective
`(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module of
`pre ++ x :: y :: post` to those of the standard module of `pre ++ y :: x :: post`
(Mœglin 1997, §§7–8 and p. 165: the normalized intertwining operator of the exchange is
bijective when the two blocks are not linked). -/
def RealUnlinkedSwapStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (x y : RealBlock),
    realRank (pre ++ x :: y :: post) = n → realBlockExponent y ≤ realBlockExponent x →
      AreRealBlocksUnlinked x y →
        ∃ T : kFiniteFunctions (realStandardModule n (pre ++ x :: y :: post))
              (unitaryCompact ℝ n) →ₗ[ℂ]
            kFiniteFunctions (realStandardModule n (pre ++ y :: x :: post)) (unitaryCompact ℝ n),
          Function.Injective T ∧
            IsRealStandardIntertwiner n (realStandardRep n (pre ++ y :: x :: post))
              (realStandardLie n (pre ++ y :: x :: post)) (pre ++ x :: y :: post) T

/-- **Intertwiners to the reversed standard module.** For a list `ds` of real blocks of total
rank `n` in Langlands order, every `(𝔤, K)`-intertwiner `T` from the `O(n)`-finite functions of
the standard module of `ds` to those of the standard module of `ds.reverse` vanishes on every
proper `(𝔤, K)`-submodule `W`. (By Langlands' theorem, Mœglin 1997, Theorem 4, the image of a
nonzero such `T` is the unique irreducible submodule of the target, isomorphic to the Langlands
quotient, which occurs with multiplicity one; so `ker T` is the largest proper submodule.) -/
def RealReverseIntertwinerKernelStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock)
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds.reverse) (unitaryCompact ℝ n))
    (W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))),
    realRank ds = n → IsRealLanglandsOrdered ds →
      IsRealStandardIntertwiner n (realStandardRep n ds.reverse) (realStandardLie n ds.reverse)
        ds T →
        IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W → W ≠ ⊤ →
          W ≤ LinearMap.ker T

/-- The Langlands-quotient statement, unlinked swaps and intertwiners to the reversed module
imply the "if" part of Speh's criterion. -/
def RealStandardIrreducibleCriterionReductionStatement : Prop :=
  RealStandardLanglandsQuotientStatement → RealUnlinkedSwapStatement →
    RealReverseIntertwinerKernelStatement → RealStandardIrreducibleCriterionStatement

/-! ## Composing intertwiners between standard modules -/

/-- The composition of two intertwiners between standard modules is an intertwiner. -/
theorem IsRealStandardIntertwiner.comp_standard {n : ℕ} {ds es fs : List RealBlock}
    {T₁ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)}
    {T₂ : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n fs) (unitaryCompact ℝ n)}
    (h₁ : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T₁)
    (h₂ : IsRealStandardIntertwiner n (realStandardRep n fs) (realStandardLie n fs) es T₂) :
    IsRealStandardIntertwiner n (realStandardRep n fs) (realStandardLie n fs) ds (T₂ ∘ₗ T₁) := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hT⟩ := h₁.1 k f
    refine ⟨hf, ?_⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hT, h₂.map_realStandardRep]
  · obtain ⟨hf, hT⟩ := h₁.2 X f
    refine ⟨hf, ?_⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hT, h₂.map_realStandardLie]

/-- There is an injective `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the
standard module of `ds` to those of the standard module of `es`. -/
def RealInjectiveIntertwinerExists (n : ℕ) (ds es : List RealBlock) : Prop :=
  ∃ T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n),
    Function.Injective T ∧
      IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T

theorem RealInjectiveIntertwinerExists.refl (n : ℕ) (ds : List RealBlock) :
    RealInjectiveIntertwinerExists n ds ds :=
  ⟨LinearMap.id, Function.injective_id, isRealStandardIntertwiner_id n ds⟩

theorem RealInjectiveIntertwinerExists.trans {n : ℕ} {ds es fs : List RealBlock}
    (h₁ : RealInjectiveIntertwinerExists n ds es) (h₂ : RealInjectiveIntertwinerExists n es fs) :
    RealInjectiveIntertwinerExists n ds fs := by
  obtain ⟨T₁, hi₁, h₁⟩ := h₁
  obtain ⟨T₂, hi₂, h₂⟩ := h₂
  exact ⟨T₂ ∘ₗ T₁, hi₂.comp hi₁, h₁.comp_standard h₂⟩

/-! ## Reversing a list by unlinked swaps -/

/-- The rank of a list of real blocks does not depend on the order of the blocks. -/
theorem realRank_perm {xs ys : List RealBlock} (h : xs.Perm ys) : realRank xs = realRank ys :=
  (h.map RealBlock.rank).sum_eq

/-- Moving a block `a` past a list `l` of blocks with smaller or equal real exponents, all
unlinked from `a`, one swap at a time. -/
theorem realInjectiveIntertwinerExists_moveToEnd (hSw : RealUnlinkedSwapStatement) (n : ℕ)
    (a : RealBlock) :
    ∀ (l pre post : List RealBlock), realRank (pre ++ a :: l ++ post) = n →
      (∀ b ∈ l, realBlockExponent b ≤ realBlockExponent a ∧ AreRealBlocksUnlinked a b) →
        RealInjectiveIntertwinerExists n (pre ++ a :: l ++ post) (pre ++ l ++ a :: post)
  | [], pre, post, _, _ => by
    simpa using RealInjectiveIntertwinerExists.refl n (pre ++ a :: post)
  | b :: l, pre, post, hrank, hl => by
    have hb := hl b List.mem_cons_self
    have e1 : pre ++ a :: (b :: l) ++ post = pre ++ a :: b :: (l ++ post) := by simp
    have e2 : pre ++ [b] ++ a :: l ++ post = pre ++ b :: a :: (l ++ post) := by simp
    have e3 : pre ++ [b] ++ l ++ a :: post = pre ++ (b :: l) ++ a :: post := by simp
    rw [e1] at hrank ⊢
    have h1 : RealInjectiveIntertwinerExists n (pre ++ a :: b :: (l ++ post))
        (pre ++ b :: a :: (l ++ post)) :=
      hSw n pre (l ++ post) a b hrank hb.1 hb.2
    have hrank' : realRank (pre ++ [b] ++ a :: l ++ post) = n := by
      rw [e2, ← hrank]
      exact realRank_perm (List.Perm.append_left pre (List.Perm.swap a b _))
    have h2 := realInjectiveIntertwinerExists_moveToEnd hSw n a l (pre ++ [b]) post hrank'
      (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    rw [e2, e3] at h2
    exact h1.trans h2

/-- Reversing a list `l` of blocks with non-increasing real exponents, pairwise unlinked, by
adjacent swaps, inside arbitrary lists `pre` and `post`. -/
theorem realInjectiveIntertwinerExists_reverse (hSw : RealUnlinkedSwapStatement) (n : ℕ) :
    ∀ (l pre post : List RealBlock), realRank (pre ++ l ++ post) = n →
      l.Pairwise (fun a b => realBlockExponent b ≤ realBlockExponent a ∧
        AreRealBlocksUnlinked a b) →
        RealInjectiveIntertwinerExists n (pre ++ l ++ post) (pre ++ l.reverse ++ post)
  | [], pre, post, _, _ => by
    simpa using RealInjectiveIntertwinerExists.refl n (pre ++ post)
  | a :: l, pre, post, hrank, hl => by
    rw [List.pairwise_cons] at hl
    have h1 := realInjectiveIntertwinerExists_moveToEnd hSw n a l pre post hrank hl.1
    have hrank' : realRank (pre ++ l ++ a :: post) = n := by
      rw [← hrank]
      have hp : (pre ++ (l ++ a :: post)).Perm (pre ++ a :: (l ++ post)) :=
        List.Perm.append_left pre List.perm_middle
      exact realRank_perm (by simpa using hp)
    have h2 := realInjectiveIntertwinerExists_reverse hSw n l pre (a :: post) hrank' hl.2
    have e : pre ++ (a :: l).reverse ++ post = pre ++ l.reverse ++ a :: post := by simp
    rw [e]
    exact h1.trans h2

/-- In a Langlands-ordered list without linked Mœglin data, every block has a real exponent
at least that of every later block and is unlinked from it. -/
theorem pairwise_exponent_unlinked {ds : List RealBlock} (hord : IsRealLanglandsOrdered ds)
    (hu : IsRealMoeglinUnlinked ds) :
    ds.Pairwise (fun a b => realBlockExponent b ≤ realBlockExponent a ∧
      AreRealBlocksUnlinked a b) := by
  unfold IsRealMoeglinUnlinked realMoeglinData at hu
  rw [List.pairwise_flatMap] at hu
  exact hord.and hu.2

/-! ## The reduction -/

/-- **The reduction.** By the Langlands-quotient statement the standard module of `ds` is
nonzero. Reversing `ds` by unlinked swaps gives an injective intertwiner `T` to the standard
module of `ds.reverse`. Every proper `(𝔤, K)`-submodule lies in `ker T = 0`. -/
theorem realStandardIrreducibleCriterionReduction :
    RealStandardIrreducibleCriterionReductionStatement := by
  intro hL hSw hRev n ds hrank hord hu
  obtain ⟨R, -, hRtop, -⟩ := hL n ds hrank hord
  obtain ⟨T, hTinj, hT⟩ : RealInjectiveIntertwinerExists n ds ds.reverse := by
    simpa using realInjectiveIntertwinerExists_reverse hSw n ds [] [] (by simpa using hrank)
      (pairwise_exponent_unlinked hord hu)
  refine ⟨?_, fun W hWK hWX => ?_⟩
  · obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hRtop)
    exact ⟨⟨x, 0, fun h => hx (h ▸ R.zero_mem)⟩⟩
  · by_cases hW : W = ⊤
    · exact Or.inr hW
    · left
      have hker := hRev n ds T W hrank hord hT ⟨hWK, hWX⟩ hW
      rw [LinearMap.ker_eq_bot.2 hTinj] at hker
      exact eq_bot_iff.2 hker

end Langlands.Archimedean
