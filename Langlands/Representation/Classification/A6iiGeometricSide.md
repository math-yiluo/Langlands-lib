# The geometric side of the head comparison

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiGeometricSide`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`).

## Helpers

- `sigmaFinSubtype`: pairs `⟨q, t⟩` with `t < len q`, as a subtype of `α × ℕ`.
- `iso_hom_surjective`: the morphism of an isomorphism of smooth representations is
  surjective.

## `geometricSide`

Hypotheses, for `0 < n`:

- `B : BlockShape n` and segment data `d' i` on its blocks;
- `A'` are supercuspidal representatives of all segments of all `d' i`, with the blocks
  irreducible quotients of `i(A', νA', …)`;
- `π i` are irreducible admissible quotients of `(d' i).induced`, and the normalized
  product `Π` of the `π i` is irreducible;
- `ex` are exponents on the segments of the concatenation `c` of the `d' i`, antitone
  inside each `d' i`;
- `m` is a merge grouping of `c` for `ex`.

Conclusion: `fineAtoms` (with representatives `A' ∘ finSigmaFinEquiv.symm`) has
positive multiplicity in the opposite Jacquet module of `Π` along `fineShape c m`.

Proof.

1. Each `d' i` is refined into its supercuspidal blocks; let `S' i` be the flattening
   of `(d' i).shape` by `BlockShape.uniform`, and `P = B.flatten S'`. Each `π i` is a
   quotient of `Ind_{S' i}(ν^t A')`. This uses three maps:
   - `nonempty_flatten_iso`, which identifies `Ind_{S' i}(ν^t A')` with the product of
     the segment inductions;
   - `productMap_surjective` of the segment quotients, onto `(d' i).induced`;
   - the head map onto `π i`.
2. Every block of `P` and of `fineShape c m` is labelled by its segment (an element of
   `Σ i, Fin (d' i).length`) and its position `t`, as an element of
   `{x : _ × ℕ // x.2 < len x.1}`. Let `e` be the permutation of the blocks of `P`
   matching the two labellings, and `hC : P.permute e = fineShape c m` the resulting
   shape equality (`BlockShape.ext_of_size`).
3. `e` keeps the order inside each factor `i` (`hstab`). Two segments of `d' i` keep
   their order because the merge is stable (`MergeGrouping.lt_of_lt`) and the exponents
   decrease inside `d' i`. Two blocks of one segment keep their position order. Hence
   `isMinimalRepresentative_permute_flatten` applies.
4. `geometricPiece` gives the reordered tensor as a subquotient of the opposite Jacquet
   module of `Π` along `P.permute e`. `isSubquotient_blockTensor_cast` moves it along
   `hC` to `fineShape c m`.
5. `fineAtoms` is irreducible (`glCuspidalTensor`). The opposite Jacquet module of the
   irreducible admissible `Π` has finite length (`oppositeJacquetFiniteLength`), so
   `count_pos_of_isSubquotient` gives the positive multiplicity.
