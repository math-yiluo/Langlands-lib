# Upper canonical Jacquet lifts for product Levis

This module proves, for the product upper radical `refinedUnipotent F.Carrier B S`
inside a product Levi `B.Levi F.Carrier`, the two canonical-lift facts that the
Library already proves for the product opposite radical in
`Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftProof`. It adds no
statement to the Library; it supports the refined clause of the proof of
`Langlands.Parabolic.NaturalNormalizedJacquetDualityStatement`. The route by
blockwise inverse transpose is internal to this project; the underlying
mathematics is Casselman's canonical lifting of Jacquet-module classes to stable
images of compression (Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
`casselman-2019-jacquet-module`, Proposition III.5.5 on page 7 with
Lemma III.5.4 on page 6), here for the upper radical of a product Levi.

## Blockwise inverse transpose

`leviInverseTranspose F T B` is the topological group automorphism of
`B.Levi F.Carrier` that applies `T.generalLinearInverseTranspose (B.size i)` in each
block `i` (built from `MulEquiv.piCongrRight`, continuous in both directions
coordinatewise). It is computed blockwise (`leviInverseTranspose_apply`) and is an
involution (`leviInverseTranspose_involutive`). It

- carries the product of the comaps of open subgroups `K i` under the blockwise
  inverse transpose back onto `CuspidalSupport.leviPiOpenSubgroup T B K`
  (`leviInverseTranspose_map_leviPiOpenSubgroup`);
- maps `refinedOppositeUnipotent F.Carrier B S` onto `refinedUnipotent F.Carrier B S`
  (`leviInverseTranspose_refinedOppositeUnipotent_map`) and `refinedLevi F.Carrier B S`
  onto itself (`leviInverseTranspose_refinedLevi_map`), from the Library
  single-block facts `inverseTranspose_mem_unipotentSubgroup_iff`,
  `inverseTranspose_mem_oppositeUnipotentSubgroup_iff` and
  `inverseTranspose_mem_leviSubgroup_iff`;
- sends the tuple of inverse block scalars `(blockScalar (a i))⁻¹` to the tuple of
  block scalars `blockScalar (a i)` (`leviInverseTranspose_blockScalar_inv`, from
  `inverseTranspose_blockScalar`).

## The two canonical-lift facts

Fix an admissible representation `ρ` of `B.Levi F.Carrier`, compact open subgroups
`K i` of the blocks with block Iwahori factorization for `S i`, and strictly
contracting exponents `a i`. Let `g` be the tuple `fun i => blockScalar (a i)`.

- `refinedPowerKernelJacquet`: the supremum of the kernels of the powers of
  compression by `g` on the `leviPiOpenSubgroup T B K`-fixed vectors equals the
  kernel of the fixed-vector Jacquet map for `refinedUnipotent` with Levi
  `refinedLevi`.
- `refinedStableImageJacquetBijective`: the fixed-vector Jacquet map for
  `refinedUnipotent` is bijective on the stable image of compression by `g`.

Both proofs are the same transport. Let `K' i` be the comap of `K i` under the
inverse transpose; it is compact (`BlockShape.inverseTranspose_compact_comap`) and
has block Iwahori factorization (`BlockShape.inverseTranspose_iwahoriFactorization`).
The composite `ρ ∘ leviInverseTranspose` is admissible
(`isAdmissible_comp_continuousMulEquiv`). The Library opposite results
`refinedOppositePowerKernelJacquet` and `refinedOppositeStableImageJacquetBijective`
apply to it at `K'` with the same exponents, for compression by the inverse tuple.
The Library group-transport theorems `powerKernelSup_eq_ker_groupTransport` and
`stableImageJacquetMap_bijective_groupTransport`, with the subgroup identities
above, carry these statements to `ρ` at `leviPiOpenSubgroup T B K` for the upper
radical, and `leviInverseTranspose_blockScalar_inv` rewrites the transported
compressing element as `g`.
