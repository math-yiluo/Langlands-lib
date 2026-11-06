# Multisegment and block-sum combinatorics of the assembly

This internal development proves unconditional facts about the data in the
assembly relation `IsAssembledFrom` of `Langlands/Correspondence/AssemblyRelation.lean`.
It uses only the published definitions `cuspidalDatumOf`, `segmentOf`,
`multisegmentOf`, `IsBlockSum`, the published Weil–Deligne pair equivalences,
blocks and direct sums, and Mathlib's list permutations. It assumes no
classification theorem and does not prove `AssemblyBijectiveStatement`. These
lemmas are the bookkeeping steps that a proof of rankwise bijectivity of the
assembly needs, apart from the classification and decomposition theorems.

Throughout, `c0 : SupercuspidalMap F` is a supercuspidal map. A block datum is
`r : ℕ`, ranks `d : Fin r → ℕ`, irreducible Weil classes
`σ i : IrreducibleWeilClass F (d i + 1)` and lengths `m : Fin r → ℕ`. The segment
`segmentOf F c0 (σ i) (m i)` starts at `c0 (σ i)` and has length `m i + 1`.

## Reindexing direct sums

The generic `WeilDeligneRepresentation.directSumReindexEquiv` and its proof
are in [DirectSumReindex](../WeilDeligne/DirectSumReindex.md). This module uses
that equivalence to match finite block sums.

## Injectivity side

- `segmentOf_injective`: if `c0 n` is injective for every `n`, then
  `segmentOf F c0 σ m = segmentOf F c0 σ' m'` implies `⟨d, σ⟩ = ⟨d', σ'⟩` as
  ranked Weil classes (a dependent pair `Σ k, IrreducibleWeilClass F (k + 1)`) and
  `m = m'`. Proof: the segment bases are equal cuspidal data, so their ranks
  `d + 1 = d' + 1` agree, which gives `d = d'`. Then their supercuspidal classes
  `c0 σ` and `c0 σ'` agree (taken as a heterogeneous equality with
  `congr_arg_heq`, then turned into an equality). Injectivity of `c0` gives
  `σ = σ'`, and the segment lengths give `m = m'`.
- `multisegmentOf_matching`: if `c0` is injective in every rank and
  `multisegmentOf F c0 σ m = multisegmentOf F c0 σ' m'`, there is a bijection
  `e : Fin r ≃ Fin r'` with `⟨d i, σ i⟩ = ⟨d' (e i), σ' (e i)⟩` and
  `m i = m' (e i)` for all `i`. Proof: equal multisets of `List.ofFn` lists come
  from permuted lists. The private lemma `ofFn_matching` turns the permutation
  into an equivalence of `Fin` index types via `List.Perm.idxBij`, and
  `segmentOf_injective` is then applied to each matched pair of segments.
- `weilClassForget_congr`: equal ranked Weil classes have equal underlying
  representation classes `weilClassForget`.
- The imported `parameterForget_injective` from `ZeroMonodromyExtension`
  states that `parameterForget F : WeilDeligneClass F n → _` is injective.
  Its field argument is implicit. Its proof recovers an equivalence of
  representatives from equality of their forgotten classes.
- `IsBlockSum.eq_of_matching`: if `D` and `D'` are rank-`n` parameter classes,
  `IsBlockSum F σ m D` and `IsBlockSum F σ' m' D'` hold, and `e` matches the two
  block data as in `multisegmentOf_matching`, then `D = D'`. Proof: for each `i`,
  the Weil representations `B i` and `B' (e i)` have equal classes, so they are
  equivalent by `FiniteRepresentation.classOf_eq_iff`. `blockEquiv` turns this into
  an equivalence of the blocks with equal lengths `m i + 1 = m' (e i) + 1`.
  `directSumEquiv` assembles these block equivalences, and
  `directSumReindexEquiv e` reindexes the right-hand direct sum. Composing with
  the given equivalences to `A` and `A'` shows that `A` and `A'` have equal
  classes, so `parameterForget_injective` gives `D = D'`.

- `IsBlockSum.eq_of_multisegmentOf_eq`: if `c0` is injective in every rank,
  `IsBlockSum F σ m D` and `IsBlockSum F σ' m' D'` hold for rank-`n` classes `D`
  and `D'`, and `multisegmentOf F c0 σ m = multisegmentOf F c0 σ' m'`, then
  `D = D'`. This combines `multisegmentOf_matching` with
  `IsBlockSum.eq_of_matching`.

## Rank identities

- `IsBlockSum.rank_eq`: if `IsBlockSum F σ m D` holds with `D` of rank `n`, then
  `n = ∑ i, (d i + 1) * (m i + 1)`. Proof: the representative `A` has rank `n`,
  and the direct sum equivalent to `A` has the same rank. That rank is the sum
  of the block ranks (`rank_directSum`), and each block has rank
  `rank (B i) * (m i + 1)` (`rank_block`), with `rank (B i) = d i + 1`.
- `degree_multisegmentOf`: the degree of `multisegmentOf F c0 σ m` is
  `∑ i, (d i + 1) * (m i + 1)`. The proof unfolds `Multisegment.degree` as the sum
  of segment degrees `length * rank` over the list `List.ofFn`.

## Surjectivity side

- `exists_segmentOf_eq`: if `c0 n` is surjective for every `n`, every segment
  `Δ : Segment.{uA, uF} F.canonicalTopologicalData` equals `segmentOf F c0 σ m`
  for some `d`, `σ` and `m`. Proof: the positive rank and length of `Δ` are
  written as `d + 1` and `m + 1`, and `σ` is a preimage under `c0 (d + 1)` of the
  supercuspidal class of `Δ`.
- `exists_multisegmentOf_eq`: under the same hypothesis, every multisegment
  `a : Multisegment.{uA, uF} F.canonicalTopologicalData` equals
  `multisegmentOf F c0 σ m` for some block datum. Proof: choose such data for
  every segment and index them by the list `a.toList`. Then
  `List.ofFn a.toList.get = a.toList`, whose multiset is `a`.

## Provenance

These are internal, derived lemmas. They have no counterpart stated separately in
the literature; Henniart's assembly of the local Langlands correspondence from its
supercuspidal part uses them implicitly. The arguments use only the published
definitions named above and introduce no external assertion.
