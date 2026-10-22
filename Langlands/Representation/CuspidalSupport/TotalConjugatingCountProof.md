# Proof of the total count of minimal conjugating block permutations

Authors: Worker 275, with Worker 165 (the proof of `levi_mem_iff` is
imported from `CuspidalSupport.MinimalConjugatingCosetsProof`).

This module proves the published proposition
`Langlands.CuspidalSupport.TotalConjugatingCountTheorem.{uF}` from
`Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement`.
That is the count `l(M) = r!` from Bernstein–Zelevinsky (1977), section 2.8.
The exported theorem is

```lean
theorem totalConjugatingCount : TotalConjugatingCountTheorem.{uF}
```

in namespace `Langlands.CuspidalSupport`. Its type is exactly the statement,
for every field universe `uF`. The module imports the statement, the shared
`BlockMap` definition and `MinimalConjugatingCosetsProof`. It adds no
hypothesis, axiom or instance to the target.

## Source count versus internal constructions

The count proved is the one in the statement. Write
`S = (C : BlockShape n) × MinimalConjugatingPermutations (F := F.Carrier) B C`.
Its elements are pairs of a target shape `C` and a permutation `w` that is
a Library minimal representative for `(B, C)` and whose actual permutation
matrix conjugates the actual embedded Levi `B.leviSubgroup` onto
`C.leviSubgroup`. Permutations are counted separately even when block sizes
repeat, and rank zero is included. The proof shows `Finite S` and
`Nat.card S = B.length !`.

BZ77 states `l(M) = r!` without proof. The block reordering below is an
internal combinatorial construction of this module, not a source object.
It parametrizes `S` by `Equiv.Perm (Fin B.length)`.

## Structure of the proof

The lemmas proved here, except the final theorem, live in namespace
`Langlands.CuspidalSupport.TotalConjugatingCount`. They are proved over an
arbitrary field `F`, or an arbitrary commutative ring where noted. The final
theorem specializes them to `F.Carrier`. Write `bB = blockIndex B` for the
map sending a coordinate to its block.

### 1. Block bookkeeping (section `Blocks`)

- The imported `Geometric.blockIndex_index`: the coordinate `B.index i a` lies in block `i`.
- `index_surjective`: every coordinate is `B.index i a` for some `i`, `a`.
- The imported `Geometric.index_strictMono`: `B.index i` is strictly increasing. It unfolds
  `B.indexEquiv` to `finSigmaFinEquiv`, whose value at `⟨i, a⟩` is the sum
  of the earlier block sizes plus `a`.
- `card_blockIndex_fiber`: block `i` has exactly `B.size i` coordinates.
  The fiber `{a // bB a = i}` is carried by `B.indexEquiv.symm` onto
  `{s : B.Index // s.1 = i}`, which `Equiv.sigmaSubtype` identifies with
  `Fin (B.size i)`.
- `shape_ext`: two block shapes with equal lengths and equal sizes (after
  `Fin.cast`) are equal. The remaining fields are proofs.

### 2. Levi membership and the conjugation criterion (sections `Matrices`, `Conjugation`)

- The imported `Langlands.CuspidalSupport.levi_mem_iff` (over a commutative ring): a matrix lies in
  `B.leviSubgroup R` exactly when its entries between coordinates in
  different blocks vanish. Forward, it uses
  `leviEmbedding_apply_ne`. Backward, the vanishing makes the matrix lie in
  the parabolic subgroup, and the Levi embedding of its Levi projection
  agrees with it entrywise. This proof is Worker 165's.
- `mem_map_conj_iff`: `h` lies in the image of `B.leviSubgroup R` under
  conjugation by `P = permutation n R w` exactly when
  `h (w a) (w b) = 0` whenever `bB a ≠ bB b`. This uses
  `(P⁻¹ h P) a b = h (w a) (w b)`, from the Library's entry formulas
  `mul_permutation_entry`, `permutation_mul_entry` and `permutation_inv`.
- `swap_entries_vanish_iff` (over a nontrivial commutative ring): for a
  labelling `β` of the coordinates and an injective `e`, the transposition
  matrix of `e u` and `e v` has all entries between `e x` and `e y` with
  `β x ≠ β y` zero exactly when `β u = β v`.
- `conjugatesLevi_iff`: `ConjugatesLevi B C w` holds exactly when for all
  coordinates `a`, `b`, `bB a = bB b ↔ bC (w a) = bC (w b)`. Forward,
  test the Levi equality on the transposition matrix of `w a` and `w b`. By
  the two previous lemmas, membership on the source side means
  `bB a = bB b`, and on the target side it means `bC (w a) = bC (w b)`.
  Backward, the two entrywise membership conditions are equivalent after
  substituting `x = w a`, `y = w b`.

### 3. The block map (section `Conjugation`)

The shared `Langlands.CuspidalSupport.blockMap B C w i` is the target block containing the image of the first
coordinate of source block `i`. Assume `ConjugatesLevi B C w`.

- `blockIndex_apply`: `bC (w a) = blockMap B C w (bB a)` for every `a`.
- `blockMap_injective`, `blockMap_surjective`, `blockMap_bijective`: these
  follow from the criterion.
- `length_eq`: `B.length = C.length`, by comparing cardinalities.
- `size_blockMap`: `C.size (blockMap B C w i) = B.size i`. The permutation
  `w` restricts to a bijection between the two block fibers, whose
  cardinalities are given by `card_blockIndex_fiber`.
- `range_block`: `w` maps source block `i` onto the target block
  `blockMap B C w i`, as sets of coordinates.

### 4. Reordering blocks (section `Reordering`)

Fix `σ : Equiv.Perm (Fin B.length)`.

- `reorderedShape B σ` has the same length as `B`, and its block `j` has size
  `B.size (σ⁻¹ j)`. Its total is `n` by `Equiv.sum_comp`.
- `reorderIndex B σ` is the equivalence of sigma index types sending
  position `a` of source block `i` to position `a` of target block `σ i`.
- `reorderPerm B σ` is the coordinate permutation
  `B.indexEquiv.symm`, then `reorderIndex B σ`, then
  `(reorderedShape B σ).indexEquiv`. It moves source block `i` onto target
  block `σ i`, keeping the order inside the block (`reorderPerm_index`,
  `reorderPerm_symm_index`, `blockIndex_reorderPerm`).
- `reorderPerm_minimal`: `reorderPerm B σ` is a Library minimal
  representative for `(B, reorderedShape B σ)`. On each source block it is
  `index_strictMono` of the target shape, and its inverse on each target
  block is `index_strictMono` of `B`.
- `reorderPerm_conjugates`: it conjugates the source Levi onto the target
  Levi, by `conjugatesLevi_iff` and `blockIndex_reorderPerm`.

### 5. The bijection and the count (section `Count`)

`reorderElement B σ` is the element `⟨reorderedShape B σ, reorderPerm B σ⟩`
of `S`. Let `blockValue x i` be the natural-number value of the block map of
`x ∈ S` at `i`. The natural-number values avoid comparing `Fin C.length`
across different target shapes.

- `blockValue_reorderElement`: the block map of `reorderElement B σ` is `σ`.
- `eq_of_blockValue_eq`: an element of `S` is determined by its block map.
  Say two elements have the same block map. Then their target shapes have
  the same length (`length_eq`) and the same block sizes (`size_blockMap`),
  so they are equal (`shape_ext`). The two permutations then map each source
  block onto the same target block (`range_block`). Both are strictly
  increasing on that block (minimality). A strictly increasing map from
  `Fin (B.size i)` is determined by its range
  (`StrictMono.range_inj_of_wellFoundedLT`). So the permutations agree on
  every coordinate.
- `reorderElement_injective`: by `blockValue_reorderElement`.
- `reorderElement_surjective`: for `x ∈ S`, take `σ` to be the block map of
  `x`, a bijection by `blockMap_bijective`, transported along
  `length_eq` by `finCongr`. Then `reorderElement B σ` and `x` have the same
  block map, so they are equal by `eq_of_blockValue_eq`.
- `finite_and_card_eq`: `S` is finite as the image of the finite type
  `Equiv.Perm (Fin B.length)`. By `Nat.card_eq_of_bijective` and
  `Nat.card_perm`, `Nat.card S = (Nat.card (Fin B.length))! = B.length !`.

At rank zero `B` has no blocks. The argument needs no special case: the
only block permutation is the identity, and the bijection gives exactly one
element of `S`.

### 6. The exported theorem

`totalConjugatingCount` introduces `p`, the `Fact p.Prime` instance, `F`,
`n` and `B`, and applies `finite_and_card_eq` with the field `F.Carrier`.
A closing `example` confirms that the theorem's type is the statement.

## Interfaces for consumers

Import `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof`.
Besides `Langlands.CuspidalSupport.totalConjugatingCount`, these lemmas in
`Langlands.CuspidalSupport.TotalConjugatingCount` hold over any field, or
any commutative ring where noted above:

- `conjugatesLevi_iff`, the partition description of `ConjugatesLevi`;
- `blockMap_bijective`, `length_eq`, `size_blockMap` and
  `range_block` for a conjugating permutation;
- `card_blockIndex_fiber`;
- `reorderElement_bijective` and `finite_and_card_eq`.

The imported `Langlands.CuspidalSupport.blockMap` and `levi_mem_iff`, and
`Langlands.Geometric.blockIndex_index` and `index_strictMono`, supply the
shared block-label definition and elementary helpers. The reordering
construction retains its convention that target block `j` is source block
`σ⁻¹ j`; `BlockShape.permute` uses the other direction of relabelling.
