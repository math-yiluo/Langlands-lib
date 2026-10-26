# Minimal conjugating permutations inside a product Levi

Module `Langlands.Representation.Classification.ProductLeviMinimalIndex`,
namespace `Langlands.ProductLeviMinimalIndex`.

## Purpose and provenance

This is an internal combinatorial helper for the product-Levi cuspidal Jacquet
multiplicity theorem
(`Langlands.ProductLeviCuspidalJacquetMultiplicityStatement`). That statement
indexes the composition factors of the opposite self-Jacquet module of a product
Levi `B.Levi = ∏ᵢ GL(B.size i)` by the literal subtype

```
{w : MinimalConjugatingPermutations C C // w.val.val ∈ blockWeyl B},   C = B.flatten S.
```

The intended tensor proof obtains, block by block, the index types
`MinimalConjugatingPermutations (S i) (S i)` of the general-linear statement for
each inner shape `S i`. This module proves that the product of these block index
types is in bijection with the restricted flattened index type. It is the
elementary Weyl-group bookkeeping behind the "derived product-Levi
specialization" of Silberger 1979, Theorem 5.4.1.1 and BZ77, Corollary 2.13(c):
the Weyl group of a product Levi is the product of the Weyl groups of its
factors, and minimal coset representatives are formed blockwise. No statement of
the literature is formalized here; the content is internal.

## Main definition

* `CoarseMinimalPermutations B S` is the literal subtype
  `{w : MinimalConjugatingPermutations (B.flatten S) (B.flatten S) // w.val.val ∈ blockWeyl B}`
  of the target statement.
* `assemble B S v` sends a family `v i : MinimalConjugatingPermutations (S i) (S i)`
  to the block-diagonal permutation `blockPermOf B (fun i => (v i).val.val)`,
  together with proofs that it is a minimal representative for the flattened
  shape, that it conjugates the flattened Levi to itself, and that it lies in
  `blockWeyl B`.
* `assembleEquiv B S :
  (∀ i, MinimalConjugatingPermutations (S i) (S i)) ≃ CoarseMinimalPermutations B S`
  is `Equiv.ofBijective` applied to `assemble`, with `assembleEquiv_apply` and
  `assemble_val` exposing its underlying permutation.

## Proof outline

1. *Flattened block labels.* `blockIndex_flatten_index` computes the flattened
   block of the coordinate `B.index i x` as `B.flattenBlockEquiv S ⟨i, blockIndex (S i) x⟩`
   (from `BlockShape.index_index_eq_flatten` and `blockIndex_index`).
   Consequently the coarse block is the outer label of the flattened block
   (`blockIndex_eq_flatten`), two coordinates of one coarse block share a flattened
   block exactly when they share an `S i` block (`blockIndex_flatten_index_eq_iff`),
   and coordinates of different coarse blocks never share a flattened block
   (`blockIndex_flatten_index_ne`). In particular the fine Weyl group lies in the
   coarse one: `blockWeyl_flatten_le : blockWeyl (B.flatten S) ≤ blockWeyl B`.
   `forall_flatten_pairs_iff` rewrites any condition on pairs of coordinates in a
   common flattened block as the same condition inside every coarse block.
2. *Block-diagonal permutations.* For `σ : ∀ i, Perm (Fin (B.size i))`,
   `blockPermOf_symm_index` and `blockPermOf_symm` show the inverse acts by the
   inverse blocks; `blockPermOf_injective` recovers the blocks; and
   `exists_blockPermOf` shows every element of `blockWeyl B` is `blockPermOf B σ`
   for some `σ` (using `exists_index_of_blockIndex_eq` and finiteness of each block).
3. *Minimality is blockwise.* Using the coordinate criterion
   `isMinimalRepresentative_iff` (order preservation of `w` on each source block and
   of `w⁻¹` on each target block), step 1, and strict monotonicity of `B.index i`
   (`index_strictMono`), `isMinimalRepresentative_blockPermOf_iff` proves that
   `blockPermOf B σ` is a minimal representative for `(B.flatten S, B.flatten S)`
   iff every `σ i` is a minimal representative for `(S i, S i)`.
4. *Levi conjugation is blockwise.* Using the combinatorial criterion
   `TotalConjugatingCount.conjugatesLevi_iff` (the permutation matrix conjugates the
   source Levi onto the target Levi iff `w` maps "same source block" exactly to
   "same target block"), `conjugatesLevi_blockPermOf_iff` proves that
   `blockPermOf B σ` conjugates the flattened Levi to itself iff every `σ i`
   conjugates the Levi of `S i` to itself. Pairs in different coarse blocks are
   handled by `blockIndex_flatten_index_ne` on both sides.
5. *Bijectivity.* `assemble_bijective`: injectivity is `blockPermOf_injective`;
   for surjectivity an element of the restricted subtype lies in `blockWeyl B`,
   hence equals `blockPermOf B σ` (step 2), and steps 3–4 give the required block
   properties of every `σ i`.

## Blockwise Levi conjugation

The section `Transport` (field `F` explicit) shows that the Levi conjugation by
an assembled block-diagonal permutation is blockwise conjugation in the
flattened product coordinates `flattenedLeviProductEquiv F B S :
(B.flatten S).Levi F ≃* ∀ i, (S i).Levi F`. This is the identification the
product-Levi proof uses to compare the transported representations indexed by
`w = blockPermOf B (fun i => v i)` with the external tensor product of the
blockwise transported representations.

* `leviEmbedding_conj_blockPermOf σ X`: for `X : B.Levi F`, embedding the
  family `P(σ i) * X i * P(σ i)⁻¹` block-diagonally gives
  `P(w) * B.leviEmbedding X * P(w)⁻¹` with `w = blockPermOf B σ` and `P` the
  permutation matrix (`GeneralLinear.permutation`). Proof: compare entries at
  `(B.index i x, B.index j y)` with `permutation_conjugate_entry`,
  `blockPermOf_symm_index`, and `leviEmbedding_apply_same` /
  `leviEmbedding_apply_ne` according to whether `i = j`.
* `flattenedLeviProductEquiv_leviConjugation σ hσ hw m`: if every `σ i`
  conjugates the Levi of `S i` to itself (`hσ`) and `blockPermOf B σ` conjugates
  the flattened Levi to itself (`hw`), then
  `flattenedLeviProductEquiv (leviConjugation C C (blockPermOf B σ) hw m) i =
  leviConjugation (S i) (S i) (σ i) (hσ i) (flattenedLeviProductEquiv m i)`.
  Proof: the nested embedding `X ↦ B.leviEmbedding (refinedLeviEquiv X)` is
  injective (`leviEmbedding_injective`, injectivity of `refinedLeviEquiv`), and
  after applying it both sides become the ambient matrix
  `P(w) * C.leviEmbedding m * P(w)⁻¹`, by `flattenedLeviEquiv_embedding`,
  `leviConjugation_embedding` (for `C` and for every `S i`) and
  `leviEmbedding_conj_blockPermOf`.
* `flattenedLeviProductEquiv_leviConjugation_symm`: the same identity for the
  inverse conjugations `(leviConjugation …).symm`, which is the convention of
  `CuspidalSupport.transport`; it follows from the previous item applied to the
  preimage.

The module uses only published results: `blockPermOf`, `blockPermOf_index`,
`blockPermOf_mem_blockWeyl`, `index_strictMono`
(`Geometric/WeylMinimalRepresentativeProof`), `exists_index_of_blockIndex_eq`
(`Geometric/WeylUniquenessProof`), `isMinimalRepresentative_iff`
(`CuspidalSupport/BlockPermutation`), `TotalConjugatingCount.conjugatesLevi_iff` and
`TotalConjugatingCount.index_surjective`
(`CuspidalSupport/TotalConjugatingCountProof`), and `BlockShape.index_index_eq_flatten`
(`CuspidalSupport/MinimalJacquetProof`), and for the transport section
`permutation_conjugate_entry` (`Group/GL/Maps`), `leviEmbedding_apply_same`,
`leviEmbedding_apply_ne`, `leviEmbedding_injective` (`Group/GL/Blocks`),
`leviConjugation_embedding` (`CuspidalSupport/LeviDefinitions`),
`refinedLeviEquiv` (`Geometric/RefinementDefinitions`), and
`flattenedLeviProductEquiv`, `flattenedLeviEquiv_embedding`
(`Geometric/FlattenedLevi`). The field `F` is arbitrary; in the index part it
enters only through the `ConjugatesLevi` predicate.
