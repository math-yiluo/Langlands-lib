import Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducibleProof
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction
import Langlands.Representation.Archimedean.ComplexTemperedSortedReduction
import Langlands.Representation.Archimedean.RealInducedSwapArithmetic
import Langlands.Representation.Archimedean.RealTiedScalarAssembly
import Langlands.Representation.Archimedean.RealSwapSurjectiveProof

/-! # Permutations of Langlands-ordered standard modules -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

local notation "RealStandard" => fun n ds =>
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
local notation "ComplexStandard" => fun n ds =>
  kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)

section Lists

variable {α : Type*} (weight : α → ℝ)

private def TiedSwap (xs ys : List α) : Prop :=
  ∃ (pre post : List α) (a b : α), weight a = weight b ∧
    xs = pre ++ a :: b :: post ∧ ys = pre ++ b :: a :: post

private theorem tiedSwap_perm {xs ys : List α} (h : TiedSwap weight xs ys) : xs.Perm ys := by
  obtain ⟨pre, post, a, b, _, rfl, rfl⟩ := h
  exact (List.Perm.swap b a post).append_left pre

private theorem tiedSwaps_cons (a : α) {xs ys : List α}
    (h : Relation.ReflTransGen (TiedSwap weight) xs ys) :
    Relation.ReflTransGen (TiedSwap weight) (a :: xs) (a :: ys) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨pre, post, b, c, htie, rfl, rfl⟩ := hstep
    exact ih.tail ⟨a :: pre, post, b, c, htie, rfl, rfl⟩

private theorem tiedSwaps_moveToFront {b : α} (pre post : List α)
    (h : ∀ a ∈ pre, weight a = weight b) :
    Relation.ReflTransGen (TiedSwap weight) (pre ++ b :: post) (b :: (pre ++ post)) := by
  induction pre with
  | nil => exact .refl
  | cons a pre ih =>
    have hmove := ih (fun c hc => h c (List.mem_cons_of_mem a hc))
    apply (tiedSwaps_cons weight a hmove).tail
    exact ⟨[], pre ++ post, a, b, h a List.mem_cons_self, rfl, rfl⟩

private theorem tiedSwaps_of_ordered_perm {xs ys : List α} (hp : xs.Perm ys)
    (hx : xs.Pairwise (fun a b => weight b ≤ weight a))
    (hy : ys.Pairwise (fun a b => weight b ≤ weight a)) :
    Relation.ReflTransGen (TiedSwap weight) xs ys := by
  induction ys generalizing xs with
  | nil =>
    obtain rfl := List.perm_nil.mp hp
    exact .refl
  | cons b ys ih =>
    obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp (hp.mem_iff.mpr List.mem_cons_self)
    have hp' : (pre ++ post).Perm ys := (List.perm_middle.symm.trans hp).cons_inv
    obtain ⟨hpre, hpost, hcross⟩ := List.pairwise_append.mp hx
    obtain ⟨hb, hy'⟩ := List.pairwise_cons.mp hy
    have htie (a : α) (ha : a ∈ pre) : weight a = weight b :=
      le_antisymm (hb a (hp'.mem_iff.mp (List.mem_append_left _ ha)))
        (hcross a ha b List.mem_cons_self)
    have hsub : (pre ++ post).Pairwise (fun a b => weight b ≤ weight a) :=
      List.pairwise_append.mpr ⟨hpre, (List.pairwise_cons.mp hpost).2,
        fun a ha c hc => hcross a ha c (List.mem_cons_of_mem b hc)⟩
    exact (tiedSwaps_moveToFront weight pre post htie).trans
      (tiedSwaps_cons weight b (ih hp' hsub hy'))

end Lists

/-- Real standard modules of two permuted Langlands-ordered lists are intertwined
by a bijective linear map. -/
theorem realStandardEquiv_of_ordered_perm {n : ℕ} {ds es : List RealBlock}
    (hp : ds.Perm es) (hn : realRank ds = n)
    (hd : IsRealLanglandsOrdered ds) (he : IsRealLanglandsOrdered es) :
    ∃ T : RealStandard n ds →ₗ[ℂ] RealStandard n es,
      Function.Bijective T ∧
        IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T := by
  have hc := tiedSwaps_of_ordered_perm realBlockExponent hp hd he
  clear hp hd he
  suffices ∀ {xs}, Relation.ReflTransGen (TiedSwap realBlockExponent) ds xs →
      ds.Perm xs ∧ ∃ T : RealStandard n ds →ₗ[ℂ] RealStandard n xs,
        Function.Bijective T ∧
          IsRealStandardIntertwiner n (realStandardRep n xs) (realStandardLie n xs) ds T from
    (this hc).2
  intro xs h
  induction h with
  | refl =>
    exact ⟨List.Perm.refl _, LinearMap.id, Function.bijective_id,
      isRealStandardIntertwiner_id n ds⟩
  | tail _ hstep ih =>
    refine ⟨ih.1.trans (tiedSwap_perm _ hstep), ?_⟩
    obtain ⟨pre, post, a, b, htie, rfl, rfl⟩ := hstep
    have hr := (realRank_perm ih.1).symm.trans hn
    obtain ⟨A, hA, hAi⟩ := ih.2
    obtain ⟨B, hB, hBi⟩ := realUnlinkedSwap n pre post a b hr htie.ge
      (RealTiedScalarAssembly.areRealBlocksUnlinked_of_eq htie)
    have hBsurj := realSwapInjectiveIntertwinerSurjective n pre post a b B hr hB hBi
    exact ⟨B.comp A, (show Function.Bijective B from ⟨hB, hBsurj⟩).comp hA,
      hAi.comp_standard hBi⟩

/-- Complex standard modules of two permuted Langlands-ordered lists are intertwined
by a bijective linear map. -/
theorem complexStandardEquiv_of_ordered_perm {n : ℕ} {ds es : List ComplexCharacterData}
    (hp : ds.Perm es) (hn : ds.length = n)
    (hd : IsComplexLanglandsOrdered ds) (he : IsComplexLanglandsOrdered es) :
    ∃ T : ComplexStandard n ds →ₗ[ℂ] ComplexStandard n es,
      Function.Bijective T ∧
        IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es)
          ds T := by
  let weight : ComplexCharacterData → ℝ := fun a => a.exponent.re
  have hc := tiedSwaps_of_ordered_perm weight hp hd he
  clear hp hd he
  suffices ∀ {xs}, Relation.ReflTransGen (TiedSwap weight) ds xs →
      ds.Perm xs ∧ ∃ T : ComplexStandard n ds →ₗ[ℂ] ComplexStandard n xs,
        Function.Bijective T ∧
          IsComplexStandardIntertwining n (complexStandardRep n xs) (complexStandardLie n xs)
            ds T from
    (this hc).2
  intro xs h
  induction h with
  | refl =>
    exact ⟨List.Perm.refl _, LinearMap.id, Function.bijective_id,
      isComplexStandardIntertwining_id n ds⟩
  | tail _ hstep ih =>
    have hp := tiedSwap_perm weight hstep
    refine ⟨ih.1.trans hp, ?_⟩
    obtain ⟨pre, post, a, b, htie, rfl, rfl⟩ := hstep
    have hr := (ih.1.trans hp).length_eq.symm.trans hn
    obtain ⟨A, hA, hAi⟩ := ih.2
    obtain ⟨B, hB, hBi⟩ := complexStandardUnlinkedSwapReduction
      complexGLTwoUnlinkedIrreducible n pre post b a hr
        (ComplexTemperedSorted.not_linked_of_re_eq htie.symm)
    exact ⟨B.comp A, hB.comp hA, hAi.comp B hBi.map_rep (fun X x => hBi.map_lie _ x)⟩

section Moeglin

private def blockOfDatum : MoeglinDatum → RealBlock
  | .character parity exponent => .character (RealJacquetFrobenius.charData parity exponent)
  | .discrete weight exponent => .induced (characterOfParams weight exponent)

private theorem exponent_of_mem_datumBlocks {a b : RealBlock}
    (h : b ∈ (realBlockMoeglinData a).map blockOfDatum) :
    realBlockExponent b = realBlockExponent a := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
  refine Eq.trans ?_ (RealTiedScalarAssembly.datumExponent_re_of_mem hd)
  cases d <;> rfl

private theorem realRank_datumBlocks (a : RealBlock) :
    realRank ((realBlockMoeglinData a).map blockOfDatum) = a.rank := by
  cases a with
  | character c => simp [realBlockMoeglinData, blockOfDatum, realRank, RealBlock.rank]
  | induced d =>
    by_cases hw : d.weight = 0 <;>
      simp [realBlockMoeglinData, hw, blockOfDatum, realRank, RealBlock.rank]

private theorem realRank_moeglinBlocks (ds : List RealBlock) :
    realRank ((realMoeglinData ds).map blockOfDatum) = realRank ds := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    simp only [realMoeglinData, List.flatMap_cons, List.map_append,
      Langlands.LocalFactor.Archimedean.realRank_append, realRank_datumBlocks, realRank_cons]
    exact congrArg (a.rank + ·) ih

private theorem moeglinBlocks_ordered {ds : List RealBlock} (h : IsRealLanglandsOrdered ds) :
    IsRealLanglandsOrdered ((realMoeglinData ds).map blockOfDatum) := by
  unfold IsRealLanglandsOrdered realMoeglinData
  rw [List.map_flatMap, List.pairwise_flatMap]
  refine ⟨fun a _ => List.pairwise_of_forall_mem_list fun x hx y hy => ?_, ?_⟩
  · rw [exponent_of_mem_datumBlocks hx, exponent_of_mem_datumBlocks hy]
  · exact h.imp fun {a b} hab x hx y hy => by
      rw [exponent_of_mem_datumBlocks hx, exponent_of_mem_datumBlocks hy]
      exact hab

private theorem realStandardModule_replace_datumBlocks (n : ℕ) (pre post : List RealBlock)
    (a : RealBlock) :
    realStandardModule n (pre ++ a :: post) =
      realStandardModule n (pre ++ (realBlockMoeglinData a).map blockOfDatum ++ post) := by
  cases a with
  | character c =>
    simp [realBlockMoeglinData, blockOfDatum, RealCharacterCrossing.charData_eta]
  | induced d =>
    by_cases hw : d.weight = 0
    · rw [realStandardModule_append_expand n pre post (.induced d)]
      simp [realBlockExpand, realBlockMoeglinData, hw, blockOfDatum]
    · simp only [realBlockMoeglinData, hw, ite_false, List.map_cons, List.map_nil,
        blockOfDatum, List.append_assoc, List.singleton_append]
      exact RealInducedSwapArithmetic.standardModule_replace_induced n pre post rfl rfl

private theorem realStandardModule_append_moeglinBlocks (n : ℕ) :
    ∀ (ds pre : List RealBlock),
      realStandardModule n (pre ++ ds) =
        realStandardModule n (pre ++ (realMoeglinData ds).map blockOfDatum)
  | [], _ => rfl
  | a :: ds, pre => by
    rw [realStandardModule_replace_datumBlocks n pre ds a,
      realStandardModule_append_moeglinBlocks n ds (pre ++ (realBlockMoeglinData a).map blockOfDatum)]
    simp [realMoeglinData, List.append_assoc]

/-- Ordered real standard modules with permuted Mœglin data admit a surjective intertwiner.
The Mœglin data forget the sign of a nonzero weight and expand a weight-zero block. -/
theorem realStandardSurjection_of_moeglin_perm {n : ℕ} {ds es : List RealBlock}
    (hp : (realMoeglinData ds).Perm (realMoeglinData es)) (hn : realRank ds = n)
    (hd : IsRealLanglandsOrdered ds) (he : IsRealLanglandsOrdered es) :
    RealSurjectiveIntertwinerExists n ds es := by
  have hd' : realStandardModule n ds =
      realStandardModule n ((realMoeglinData ds).map blockOfDatum) := by
    simpa using realStandardModule_append_moeglinBlocks n ds []
  have he' : realStandardModule n es =
      realStandardModule n ((realMoeglinData es).map blockOfDatum) := by
    simpa using realStandardModule_append_moeglinBlocks n es []
  obtain ⟨T, hT, hTi⟩ := realStandardEquiv_of_ordered_perm (hp.map blockOfDatum)
    ((realRank_moeglinBlocks ds).trans hn) (moeglinBlocks_ordered hd) (moeglinBlocks_ordered he)
  exact (RealSurjectiveIntertwinerExists.of_eq hd').trans
    ((show RealSurjectiveIntertwinerExists n _ _ from ⟨T, hT.2, hTi⟩).trans
      (RealSurjectiveIntertwinerExists.of_eq he'.symm))

end Moeglin

end Langlands.Archimedean
