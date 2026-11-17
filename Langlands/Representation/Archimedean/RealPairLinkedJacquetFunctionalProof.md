# Two linked blocks: proof of `RealPairLinkedJacquetFunctionalStatement`

Lean module: `Langlands.Representation.Archimedean.RealPairLinkedJacquetFunctionalProof`,
namespace `Langlands.Archimedean`.

This module proves the Library statement `RealPairLinkedJacquetFunctionalStatement` (module
`RealLinkedJacquetPairReduction`) as the theorem
`Langlands.Archimedean.realPairLinkedJacquetFunctional`. It imports `RealInterlacedMirror`, and
through it `RealBlockFlatJacquet` and the Library module `RealCharacterCrossing`.

## The statement

For real blocks `x`, `z` (each a character, or an induction block of nonzero weight) with
`Re t(z) ≤ Re t(x)` whose Mœglin data are linked, `RealLinkedJacquetFunctionalExists r [x, z]`
holds, where `r = realRank [x, z]`. That is, the `O(r)`-finite functions of
`realStandardModule r [x, z]` carry a nonzero real Jacquet functional `ℓ` with exponents `a`, signs
`e`, a position `p` with `p + 1 < r` and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and
`ℓ(π(1 ⊗ E_{p+1,p})^k v) = 0` for every `v`.

## The proof

The Library theorem `realPairLinkedJacquetFunctional_of_kinds` splits the statement into the four
kinds of pairs, by cases on `x` and `z`. Each kind is proved in this development:

* **CC**, two characters `c`, `d` with `Re t(d) ≤ Re t(c)`:
  `realCharacterPairLinkedJacquetFunctional : RealCharacterPairLinkedJacquetFunctionalStatement`
  (this module). The list `[character c, character d]` consists of characters
  (`IsCharacterList`). It is Langlands-ordered, because `IsRealLanglandsOrdered` of a two-element
  list is the exponent inequality. Its Mœglin data are not pairwise unlinked: `realMoeglinData` of
  the list is `[datum c, datum d]`, so `IsRealMoeglinUnlinked` reduces by `simp` to the negation
  of the hypothesis `¬ AreRealBlocksUnlinked`. Then the Library theorem
  `realCharacterLinkedJacquetFunctional` (module `RealCharacterCrossing`, Worker 5731) for `n = 2`
  gives the functional. Its rank hypothesis `realRank [c, d] = 2` holds by `rfl`.
* **IC**, an induction block `d` of nonzero weight then a linked character `c`:
  `RealBlockFlatJacquet.realInducedCharacterLinkedJacquetFunctional` (module
  `RealBlockFlatJacquet`).
* **CI**, a character `c` then a linked induction block `d` of nonzero weight:
  `RealBlockFlatJacquet.realCharacterInducedLinkedJacquetFunctional` (module
  `RealBlockFlatJacquet`).
* **II**, two linked induction blocks of nonzero weights:
  `realInducedInducedLinkedJacquetFunctional` (module `RealInterlacedMirror`). It combines the
  separated case (`separatedInducedInducedLinkedJacquetFunctional`, module `RealBlockFlatJacquet`)
  with the interlaced case (`realInterlacedInducedInducedLinkedJacquetFunctional`, module
  `RealInterlacedMirror`).

`realPairLinkedJacquetFunctional` is `realPairLinkedJacquetFunctional_of_kinds` applied to these
four theorems.

The module compiles with no errors or warnings. `realPairLinkedJacquetFunctional` uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The split into four kinds is the Library's (`RealLinkedJacquetPairReduction`). The CC case is a
specialization of Worker 5731's character case of S2. The other three kinds are proved by the
flat-multiplier and interlaced methods of `RealBlockFlatJacquet.md` and `RealInterlacedMirror.md`
(Worker 5667, Task 7070). These follow the cases of the Library's `RealLinkedJacquetFunctional.md`
but do not use intertwining operators.
