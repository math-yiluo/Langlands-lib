# Shifted spherical lists and sorting by unlinked swaps

Lean module: `Langlands.Representation.Archimedean.RealDiscreteShiftSort`, part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). The shift declarations are in the namespace
`Langlands.Archimedean.RealDiscreteShift`; the transport and sorting declarations are in
`Langlands.Archimedean.RealDiscreteSort`.

## Purpose and provenance

The module proves no statement of record. It provides two tools; all declarations are
internal.

* **Shifts.** A principal series whose characters carry the signs `(−1)^{h_i}` is the twist of
  an even principal series by a product of bottom minors, where `h_i` counts the row sets that
  contain `i`. This supplies the hypothesis `IsMinorShift` of `RealDiscreteMinorCyclic`.
* **Sorting.** If every out-of-order pair of a list of characters is unlinked, the Langlands
  ordered rearrangement of the list maps onto it. So spherical cyclicity, which is stated for
  Langlands-ordered lists, transfers to the list.

## Notation

`colSet`, `IsBottom`, `IsPrincipal`, `rowWeight`, `IsMinorShift` are as in
`RealDiscreteTightness`, `RealTiedMinorProduct`, `RealTiedMinorScalar` and
`RealDiscreteMinorCyclic`. `HasGKSurjection`, `IsGKMap` and the unlinked swaps are from
`RealDiscretePresentation`. `realPositionExponent ds i` and `realPositionCharacter ds i` are the
exponent and the character of the `i`-th coordinate of the principal series of `ds` (Library).

## Shifts (`RealDiscreteShift`)

* `hits R i = |colSet R i|`, the number of `j` with `i ∈ R_j`.
* `shiftList n ds R`: the list of even characters `|·|^{e_i − h_i}`, `e_i =
  realPositionExponent ds i`. `shiftList_length`, `shiftList_parity`, `shiftChar_apply`.
* `posChar_shift`: if `χ_{ds,i}(−1) = (−1)^{h_i}` for all `i`, then
  `χ_{ds,i}(x) = |x|^{e_i − h_i} · x^{h_i}`. The character of a principal-series coordinate is
  determined by its sign and its exponent (Library `isSignedPower`).
* `rowWeight_eq`: `rowWeight R a = ∏_i a_i^{h_i}` (exchange of the products over `j` and `i`).
* `isMinorShift_shiftList`: if `ds` is principal, all `R_j` are bottom segments and the sign
  condition holds, then `IsMinorShift n ((shiftList n ds R).map character) ds R`. The character
  identity is `posChar_shift` multiplied over `i`, with `rowWeight_eq`.

## Transport and sorting (`RealDiscreteSort`)

* `isGKMap_iff`: unfolds `IsGKMap` into commutation with `O(n)` and with the complexified Lie
  algebra (Library `InductionStages.isRealStandardIntertwiner_iff`).
* `cyclic_map`: a surjective `(𝔤, K)`-intertwiner `q` maps an `O(n)`-fixed vector `T` that
  generates under the Lie algebra to an `O(n)`-fixed vector `q T` that generates under the Lie
  algebra. Proof: the preimage of a Lie-stable `W ∋ q T` is Lie-stable and contains `T`, so it
  is everything; surjectivity gives `W = ⊤`.
* `LangRel a b := Re b ≤ Re a` (exponents), with its decidability, totality and transitivity
  instances; `List.insertionSort LangRel` sorts by decreasing real exponent.
* `hasGKSurjection_orderedInsert`: inserting `c` into `S` and moving it back to the front. If `c`
  is unlinked with every `b ∈ S` with `Re c < Re b`, then
  `pre ++ orderedInsert c S ++ post ↠ pre ++ c :: S ++ post`. Induction on `S`: when `c` passes
  `b`, the swap of `b, c` (`hasGKSurjection_swap`) is used.
* `hasGKSurjection_insertionSort` (**sorting**): if every pair `c` before `b` in `L` with
  `Re c < Re b` is unlinked, then `pre ++ insertionSort L ++ post ↠ pre ++ L ++ post`.
  Induction on `L`, using the previous lemma.
* `isRealLanglandsOrdered_insertionSort`: the sorted list is Langlands ordered
  (`List.pairwise_insertionSort`).
* `datumExponent_im_of_linked`, `unlinked_of_im_ne`, `unlinked_of_block_im_ne`: linked Mœglin
  data have exponents with a real difference (every case of `MoeglinDatum.IsLinked` writes the
  difference as a real number), so data whose exponents have different imaginary parts are
  unlinked.
