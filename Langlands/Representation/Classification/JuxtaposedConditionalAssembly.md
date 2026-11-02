# Conditional assembly of the juxtaposed case of Zelevinsky's Proposition 4.6

Author: Worker 1032.

This internal planning module of the proof of
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure`
(Zelevinsky 1980, Proposition 4.6, step (1), juxtaposed case) makes no literature
assertion of its own. It derives the target proposition from five explicit
hypotheses. It is not the exact proof: that proof must replace every hypothesis by
a proved, independently accepted Library input.

Notation: `π = ⟨Δ⟩ × ⟨Δ'⟩ = d.induced` with `Δ = d.segments 0` and
`Δ' = d.segments 1`. `ρ = Δ'.base` has rank `r`, `q = Δ.length` and
`l = Δ'.length`. `J` is the normalized Jacquet functor along the uniform shape
`(r, …, r)` with `q + l` blocks, and `τ_{S_id}` is the identity shuffle tensor
`A ⊗ νA ⊗ … ⊗ ν^(q+l-1) A`.

## Hypotheses of the main theorem

- `hS1 : TwoSegmentSocleShuffleJacquet` (the shuffle count of `J(π)`, a Library
  statement from task efe00a4a-423f-449a-acf6-4e7e0eaf7f35; its exact-proof task is
  343ddfde-e74c-46b8-a559-0c8f3a3145a6).
- `hnon : ∀ n, NonassociatedJacquetSubquotientsTheorem F T n` (BZ77 2.13(b), a
  Library statement). Its proof `CuspidalSupport.nonassociatedJacquetSubquotients`
  (module `CuspidalSupport.NonassociatedJacquetSubquotientsProof`, task
  b17b8c8c-858b-4b48-994b-e3641cb05f02, artifact 8c6610e7) is published, and
  `juxtaposedSegmentSocleReverseProductStructure_of_irreducible` does not take
  `hnon`.
- `hfull : SegmentSubrepresentationFullJacquet` (Zelevinsky 1980, 3.1, a Library
  statement). It is the first clause of the published
  `segmentFullJacquetFormula F T` (module `Classification.SegmentFullJacquetProof`,
  task b331611c-526d-4925-87fe-ea67ed6e6fed, artifact f2c2886a), and
  `juxtaposedSegmentSocleReverseProductStructure_of_irreducible` does not take
  `hfull`.
- `hirr`: for every positive `r`, every supercuspidal representation `A` of `GL_r`
  and natural numbers with `b + 1 < a`, the product `ν^a A × ν^b A` along
  `BlockShape.uniform 2 r` is irreducible. The final proof derives it from Zelevinsky
  1980, Proposition 1.11(a), by `uniform_two_isIrreducible_of_nonadjacent` (module
  `JuxtaposedNonadjacentPairIrreducible`), which this module does not import.
- `hH` (part H of the plan): for every datum `d` as in the target, the beginning of
  `Δ` is `ν^(Δ'.length)` times the beginning of `Δ'`, and there are `U`, `I` and `e`
  with the four first clauses of the target. Moreover `e` has one segment, with
  beginning `Δ'.base` and length `Δ.length + Δ'.length`, and every irreducible
  quotient `π/K` (`quotientRep K ⊤`) is equivalent to `e.induced`.

## Results

- `sum_fin_eq_two`: a sum over `Fin m` with `m = 2` has its two terms.
- Four facts about invariant subspaces of a representation `ρ` over a field:
  - `quotientRepBotEquiv K`: the successive quotient `K / ⊥` (`quotientRep ⊥ K`) is
    equivalent to the representation on `K`;
  - `topSubrepresentationEquiv ρ`: the representation on `⊤` is equivalent to `ρ`;
  - `subrepresentation_ne_bot_of_isIrreducible`: an irreducible invariant subspace
    is not `⊥`;
  - `eq_bot_or_eq_of_le_isIrreducible`: an invariant subspace contained in an
    irreducible invariant subspace `K` is `⊥` or `K`.
- `bot_ne_top_induced`: under `hS1`, the lattice of subrepresentations of `π` has
  `⊥ ≠ ⊤`.
- `exists_filtration_core`: in the normalized setting (`d` on `GL_((q+l) r)`, with
  beginnings `ν^l ρ` and `ρ` and lengths `q, l > 0`), assume `hS1`, `hnon`,
  `hswap`, a representation `σ` with `J(σ) ≃ τ_{S_id}`, and that every irreducible
  quotient of `π` is equivalent to `σ`. Then there is a two-step filtration `s` of
  `π` with simple factors, graded piece 1 equivalent to `σ`, graded piece 0 not
  equivalent to `σ`, and every irreducible subrepresentation equal to
  `s.subrepresentation 1`.
- `juxtaposedSegmentSocleReverseProductStructure_of_inputs`: the target
  proposition, from `hS1`, `hnon`, `hfull`, `hirr` and `hH`.
- `juxtaposedSegmentSocleReverseProductStructure_of_irreducible`: the target
  proposition from `hS1` and `hirr` alone. It supplies `hnon` and `hfull` by the
  published proofs named above, and `hH` as
  `JuxtaposedShuffle.exists_juxtaposedUnionHead T hex` (Worker 167, module
  `Classification.JuxtaposedUnionHead`), whose conclusion is exactly `hH`. Here
  `hex : SegmentZelevinskyConstituentExistence F T` (Zelevinsky 1980, 3.1 and 3.4,
  existence of the segment constituent `⟨Δ⟩` with its strong socle and head) is the
  published `segmentZelevinskyConstituentExistence F T` (module
  `Classification.SegmentZelevinskyConstituentExistenceProof`, task 4ca79bbd,
  artifact 7172c4a6).

## Proofs

The four facts about invariant subspaces are direct. In `quotientRepBotEquiv K`
the submodule divided out, `lower ⊥ K`, is zero, so `Submodule.quotEquivOfEqBot`
is a linear equivalence; it commutes with the actions on representatives of
classes. `topSubrepresentationEquiv ρ` is the coercion from `⊤` to the whole
space, with inverse `v ↦ ⟨v, mem_top⟩`. If `K = ⊥`, every vector of `K` is zero,
so the lattice of `K` has `⊥ = ⊤`, which an irreducible representation excludes.
For `L ≤ K` with `K` irreducible, the preimage of `L` under the inclusion of `K`
(`LengthTwo.comap`) is `⊥` or `⊤` in the lattice of `K`. In the first case every
vector of `L` is zero, and in the second every vector of `K` lies in `L`.

`bot_ne_top_induced`: by the first clause of `hS1`, `J(π)` has a composition
series of length `C(q+l, q) > 0`. Its first step is a covering
(`hasSimpleFactors_iff_covBy`), so its first two terms differ. If `⊥ = ⊤` in the
lattice of `π`, every vector of `π` is zero. Every vector of `J(π)` is the image of a
vector of `π` (`jacquetMk_surjective`), so every subrepresentation of `J(π)` is
`⊥`, and the two terms are equal. This is a contradiction.

`exists_filtration_core`:

1. `eq_of_ne_bot_of_ne_top_induced` (from `JuxtaposedUniqueProperSub`): two
   subrepresentations that are neither `⊥` nor `⊤` are equal.
2. `not_nonempty_equiv_of_ne_bot` (from `JuxtaposedUnionSeparation`): no nonzero
   subrepresentation of `π` is equivalent to `σ`.
3. There is a subrepresentation `K ≠ ⊥, ⊤`. Otherwise, with `⊥ ≠ ⊤`
   (`bot_ne_top_induced`), `π` is irreducible. Then `π/⊥` is an irreducible
   quotient, equivalent to `σ` by the head hypothesis. But `π/⊥ ≃ ⊤ ≃ π`
   (`quotientRepBotEquiv ⊤`, `topSubrepresentationEquiv`), so `⊤` is equivalent
   to `σ`, which contradicts step 2 for `X = ⊤`.
4. By step 1, `⊥ ⋖ K` and `K ⋖ ⊤`: anything strictly between would be another
   subrepresentation other than `⊥` and `⊤`. So `LengthTwo.twoStep K` has simple
   factors (`twoStep_hasSimpleFactors`).
5. Graded piece 1 is `π/K`, which is irreducible because `K ⋖ ⊤`, hence equivalent
   to `σ` by the head hypothesis. Graded piece 0 is `K/⊥ ≃ K`
   (`quotientRepBotEquiv K`), which is not equivalent to `σ` by step 2.
6. An irreducible subrepresentation `K'` is nonzero
   (`subrepresentation_ne_bot_of_isIrreducible`). It is not `⊤`: otherwise `K ≤ K'`
   forces `K = ⊥` or `K = ⊤` (`eq_bot_or_eq_of_le_isIrreducible`). By step 1,
   `K' = K`.

`juxtaposedSegmentSocleReverseProductStructure_of_inputs`: take `U`, `I`, `e` and
the first four clauses from `hH`. For the filtration, generalize `ρ = Δ'.base`, a
representative `A` of `ρ` (from `HasSegmentSocles` of `Δ'`), `q` and `l`. The
degree sum of `d` (`sum_fin_eq_two`) together with `Δ.base = ρ.twist l` gives
`n = (q + l) r`; substitute `n`. Then:

- `Δ'.base = ρ.twist 0` (`CuspidalDatum.twist_zero`);
- `hswap` is `segmentFactor_swap_of_isIrreducible'` applied to `hirr`;
- `J(e.induced) ≃ τ_{S_id}` comes from `nonempty_jacquet_single_equiv` (with
  `hfull`) and `shuffleFactors_idShuffle`.

Finally apply `exists_filtration_core` with `σ = e.induced.representation` and the
head clause of `hH`.

`juxtaposedSegmentSocleReverseProductStructure_of_irreducible` applies the previous
theorem with `hnon n := CuspidalSupport.nonassociatedJacquetSubquotients F T n`,
`hfull := (segmentFullJacquetFormula F T).1` and
`hH n d h₂ hd hp hj := exists_juxtaposedUnionHead T hex d h₂ hd hp hj`, where
`hex := segmentZelevinskyConstituentExistence F T`.
