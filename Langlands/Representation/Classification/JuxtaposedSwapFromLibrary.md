# Swapping an irreducible two-block product along the uniform shape

Author: Worker 1032.

This internal helper of the proof of
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure`
(Zelevinsky 1980, Proposition 4.6, step (1), juxtaposed case) makes no literature
assertion of its own. It derives the two-block swap hypothesis `hswap` of
`Classification.JuxtaposedShuffleInducedIso` from the Library theorem
`Langlands.Classification.irreducibleTwoFactorProductSwap`, which proves the
irreducible equal-rank case of Zelevinsky 1980, Theorem 1.9 (printed p.174), in the
form "if `α × β` is irreducible then `α × β ≅ β × α`". Irreducibility of the
products is still an explicit hypothesis `hirr`.

The Library theorem uses the shape `Shahidi.twoBlocks r r` on `GL_(r+r)`. The
shuffle isomorphisms use `BlockShape.uniform 2 r` on `GL_(2*r)`. These are different
types, because `r + r` and `2 * r` are not definitionally equal. This file
transports the swap from one shape to the other.

## Results

- `productFunctor_obj_eq_of_heq`: if two block shapes `B = C` are equal and the
  factor families are heterogeneously equal, the normalized products
  `(normalizedProductInductionFunctor B).obj A` and
  `(normalizedProductInductionFunctor C).obj A'` are equal.
- `rankCast_isIrreducible_iff`: for `h : m = n` and a shape `B` on `GL_m`, the
  product along `B.rankCast h` is irreducible iff the product along `B` is.
- `rankCast_nonempty_iso`: an isomorphism of two products along `B` gives an
  isomorphism of the same products along `B.rankCast h`.
- `twoBlocks_rankCast_eq_uniform`: `(Shahidi.twoBlocks r r).rankCast (2 * r = r + r)`
  is equal to `BlockShape.uniform 2 r`.
- `twoBlockFactors_heq`: the family `twoBlockFactors σa σb` is heterogeneously equal
  to `![σa, σb]` indexed by the blocks of `uniform 2 r`.
- `uniform_two_swap_of_isIrreducible'`: fix `r > 0` and irreducible smooth
  representations `σa, σb` of `GL_r`. If `σa × σb` along `uniform 2 r` is
  irreducible, then `σa × σb ≅ σb × σa` along `uniform 2 r`.
- `segmentFactor_swap_of_isIrreducible'`: for a supercuspidal representation `A` of
  `GL_r`, assume `ν^a A × ν^b A` along `uniform 2 r` is irreducible for all natural
  numbers `a, b` with `b + 1 < a`. Then `ν^a A × ν^b A ≅ ν^b A × ν^a A` whenever `b + 1 < a`. This is
  the form `hswap` takes.

Unlike `uniform_two_swap_of_isIrreducible` in `JuxtaposedTwoBlockSwap`, these
results do not assume `TwoFactorProductConstituentCommutativity`.

## Proofs

The three cast lemmas are proved by `subst`. After substituting `h`, the cast
`B.rankCast rfl` is definitionally `B`, so both sides agree by `rfl` or by the given
isomorphism. In `productFunctor_obj_eq_of_heq`, substituting `B = C` turns the
heterogeneous equality into an equality of families.

`twoBlocks_rankCast_eq_uniform`: both shapes have two blocks. Their size functions
are `![r, r]` and `fun _ => r`, which agree at both indices by `rfl`. The remaining
fields are proofs, so `congr 1` and function extensionality finish the proof.
`twoBlockFactors_heq` is checked the same way, one index at a time.

`uniform_two_swap_of_isIrreducible'`: by the shape equality and
`twoBlockFactors_heq`, the products along `uniform 2 r` are equal to the products
along `(twoBlocks r r).rankCast _` of `twoBlockFactors σa σb` and
`twoBlockFactors σb σa`. By `rankCast_isIrreducible_iff`, irreducibility moves to
the product along `twoBlocks r r`. There `irreducibleTwoFactorProductSwap` gives the
isomorphism, `rankCast_nonempty_iso` moves it back to the cast shape, and composing
with `eqToIso` of the two product equalities gives the result.

`segmentFactor_swap_of_isIrreducible'`: the factors `ν^a A` and `ν^b A` are
irreducible, by the first component of the property of
`segmentSupercuspidalFactor`. Then apply `uniform_two_swap_of_isIrreducible'`.
