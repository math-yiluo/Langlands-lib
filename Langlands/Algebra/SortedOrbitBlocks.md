# Orbit blocks of a finite action sorted by an invariant key

Provenance: internal helper for the even-chain Galois data proof (Task 5375).
That target is derived from Robert Steinberg, *Regular elements of semi-simple
algebraic groups*, Publ. Math. IHÉS 25 (1965), 49–80 (source
`steinberg-1965-regular-elements-semisimple-groups`); the Markdown of the
target `EvenChainGaloisDataStatement` gives the full source account. In 9.4
(printed pp.72–73) Steinberg groups the simple roots into Galois orbits and
treats each orbit as one block. Sorting these blocks by their distance from
the middle of their path is not in Steinberg. It serves the derived target
condition `SplitPinning.EvenChainData.IsMiddleOut` on the ordering of the
simple roots outside the merged pairs. This module proves the needed sorting
facts as an internal derived result. The construction extends the published
`Algebra.FiniteActionOrbitBlocks.blocks` (in `SteinbergGaloisOrbitBlocks`).

Throughout, `Γ` is a group acting on a finite type `I`, and `key : I → ℕ`.

## Definitions

- `blockKey I key l`: the key of the first entry of the list `l`, and `0` for
  the empty list.
- `sortedBlocks Γ I key`: the published list of orbit blocks `blocks Γ I`,
  sorted by `List.mergeSort` with respect to `blockKey l ≤ blockKey l'`.
- `sortedOrdering Γ I key : Fin (sortedBlocks Γ I key).flatten.length ≃ I`:
  the enumeration of `I` that lists the sorted blocks one after another.

## Statements

- `sortedBlocks_perm`: `sortedBlocks` is a permutation of `blocks Γ I`.
  `mem_sortedBlocks`: both lists have the same members.
- `sortedBlocks_flatten_nodup` and `mem_sortedBlocks_flatten`: the flattened
  sorted list has no duplicates and contains every element of `I`.
- `sortedBlocks_flatten_eq_ofFn`: the flattened sorted list is
  `List.ofFn (sortedOrdering Γ I key)`.
- `sortedBlocks_invariant`: for `σ : Γ` and a sorted block `l`, the list
  `l.map (σ • ·)` is a permutation of `l`.
- `sortedBlocks_same_orbit`: two entries of one sorted block lie in one orbit.
- `blockKey_eq`: if `key` is `Γ`-invariant, the key of a sorted block is the
  key of each of its entries.
- `sortedBlocks_flatten_pairwise`: if `key` is `Γ`-invariant, the keys along the
  flattened sorted list are weakly increasing.
- `sortedOrdering_lt_of_key_lt`: if `key` is `Γ`-invariant and the key of
  `sortedOrdering j` is strictly smaller than the key of `sortedOrdering j'`,
  then `j < j'`.

## Implemented proof

The permutation, membership, no-duplicate and invariance statements transfer the
published statements for `blocks Γ I` along `List.mergeSort_perm`. The ordering
is `List.Nodup.getEquivOfForallMemList`, so the flattened list equals
`List.ofFn` of the ordering by `List.ofFn_get`.

For an invariant key, each block is one orbit, so all of its entries have the
same key, and that key is `blockKey` (`blockKey_eq`). `List.pairwise_mergeSort`
with the total preorder `≤` on block keys shows that the blocks are sorted.
`List.pairwise_flatten` then gives weakly increasing keys within each block
(the keys are equal) and between blocks. Rewriting the flattened list as
`List.ofFn` (`List.pairwise_ofFn`), a strict key inequality excludes `j = j'`
and `j' < j`.
