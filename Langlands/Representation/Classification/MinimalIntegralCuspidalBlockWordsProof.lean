import Langlands.Representation.Classification.MinimalIntegralCuspidalBlockWordsStatement
import Langlands.Representation.Classification.IntegralCuspidalConstituentWordProof
import Langlands.Representation.Classification.IntegralCuspidalWordConcatenation
import Langlands.Combinatorics.LexMinimalBlockWords
import Mathlib.Data.List.Forall2

/-! A least global actual word forces every decreasing block word. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

theorem minimalIntegralCuspidalBlockWords :
    MinimalIntegralCuspidalBlockWords.{uF,uV} F T := by
  let := T.topology
  intro m n A B S C e X π hlabels hXi hXinner hX hsorted hmin
  classical
  choose w hw hp using fun i =>
    integralCuspidalConstituentWord F T m (B.size i) (B.positive i)
      A (S i) (C i) (e i) (hlabels i) (X i) (hXi i) (hXinner i)
  have hpblocks : List.Forall₂ List.Perm (List.ofFn w)
      (List.ofFn (fun i => List.ofFn (e i))) := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro j hj hk
    simpa using hp ⟨j, by simpa only [List.length_ofFn] using hj⟩
  have hcat := integralCuspidalJacquetWord_concatenate F T
    m n A B π X w hX hw
  have heq : List.ofFn w = List.ofFn (fun i => List.ofFn (e i)) :=
    Combinatorics.eq_blocks_of_minimal_flatten hpblocks
      (by
        intro s hs
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
        exact hsorted i)
      (hmin _ hcat (List.Perm.flatten_congr hpblocks))
  have hwords := List.ofFn_inj.mp heq
  intro i
  rw [← congrFun hwords i]
  exact hw i

end Langlands.Classification
