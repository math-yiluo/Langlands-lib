import Langlands.Global.Factors.CuspidalSupportEveryPlaceStatement

/-!
# The cuspidal-support map from existence at every place and finite uniqueness

A proof of `Langlands.Global.CuspidalSupportDataReductionStatement`: existence of cuspidal
supports at every place (`CuspidalSupportEveryPlaceStatement`) together with uniqueness of
finite cuspidal supports up to a permutation (`CuspidalSupportUniquenessStatement`) gives
every irreducible automorphic operator subquotient of `GL_(r+1)` exactly one cuspidal
support in `IsobaricData F`. Both inputs are hypotheses of the statement; neither is proved
here. See the paired Markdown.
-/

set_option autoImplicit false

universe u

namespace Langlands.Global

open Automorphic (PositiveRankCuspidalClass)

/-- **Reduction of the cuspidal-support map** (Getz–Hahn 2024, Theorem 10.7.1 with
Corollary 10.7.3 and the sentence after it). Existence: the cuspidal data supplied by the
first hypothesis witness the multiset of their classes. Uniqueness: the finite conjuncts of
two witnesses give, by the second hypothesis, a bijection of index sets matching the
classes, so the two multisets of classes agree. -/
theorem cuspidalSupportDataReduction : CuspidalSupportDataReductionStatement.{u} := by
  intro hEvery hUnique F _ _ _ r Q
  obtain ⟨k, m, hm, T, P, h, hQ⟩ := hEvery F r Q
  refine ⟨Finset.univ.val.map
      (fun i => (⟨m i, (T i).isoClass⟩ : PositiveRankCuspidalClass F)),
    ⟨k, m, hm, T, P, h, hQ, rfl⟩, ?_⟩
  rintro D ⟨k', m', hm', T', P', h', hQ', rfl⟩
  obtain ⟨e, he⟩ := hUnique F r k' k m' m hm' hm T' T P' P h' h Q hQ'.1 hQ.1
  calc Finset.univ.val.map
        (fun i => (⟨m' i, (T' i).isoClass⟩ : PositiveRankCuspidalClass F))
      = Finset.univ.val.map
          ((fun j => (⟨m j, (T j).isoClass⟩ : PositiveRankCuspidalClass F)) ∘ e) := by
        congr 1
        funext i
        exact he i
    _ = (Finset.univ.val.map e).map
          (fun j => (⟨m j, (T j).isoClass⟩ : PositiveRankCuspidalClass F)) :=
        (Multiset.map_map _ _ _).symm
    _ = Finset.univ.val.map
          (fun j => (⟨m j, (T j).isoClass⟩ : PositiveRankCuspidalClass F)) := by
        rw [Multiset.map_univ_val_equiv]

end Langlands.Global
