# Adjacent filtrations involving induction blocks of weight zero

Module: `Langlands.Representation.Archimedean.RealInducedPairWeightZero`.
Namespace: `Langlands.Archimedean.RealInducedPairWeightZero`.

This internal module treats the case of two induction blocks of weight zero of
`RealInducedInducedFiltrationStatement`.
It also supplies two fusion rules for treating a single induction block of weight zero
once the adjacent steps for its two characters are available. The rules and the theorem
allow arbitrary lists before and after the exchanged blocks.

For `d : ComplexCharacterData`, `first d` and `second d` are the real characters with
exponent `d.exponent` and sign parity `1` and `0`, respectively. If `d.weight = 0`,
the Library's `realStandardModule_append_expand` identifies an occurrence of
`RealBlock.induced d` with these two character blocks, by equality of spaces of functions.
The same identification holds on the `O(n)`-finite functions by `kf_append_expand`.

`fuse_right` assumes the two adjacent filtrations moving a block `x` first past
`character (first d)` and then past `character (second d)`. It proves the filtration
moving `x` past `induced d`. `fuse_left` assumes the two adjacent filtrations moving
`character (second d)` and then `character (first d)` past a block `y`. It proves
the filtration moving `induced d` past `y`. These rules have the explicit premise
`d.weight = 0`; they do not treat induction blocks of nonzero weight.

Both proofs use the published `HasFiltration.bind` to refine the exchanged piece
of the first filtration by the second one. The fully exchanged character list
is replaced with the exchanged induction block using equality of its function
space (`HasFiltration.of_eq_pieces`). An improved piece from either step stays
an improved piece of the fused filtration: the untouched character contributes
its exponent to the support and contributes zero to the sum of squared weights.
The support changes only by a list permutation. The target identification uses
`HasFiltration.congr`. Thus the construction retains intertwining modulo earlier
ranges and the spanning property, not just the conditions on piece lists.

`both_zero` has no unproved filtration premise. For any `n`, surrounding lists
`pre`, `post` and induction data `d`, `e` of weight zero, of total rank `n`, with
`realBlockExponent (induced d) < realBlockExponent (induced e)`, it proves
`RealAdjacentFiltration n pre post (induced d) (induced e)`. It applies the two
fusion rules and discharges all four character steps with the published theorem
`Langlands.Archimedean.realCharacterPairFiltration`. In particular it treats
the double-zero case of `RealInducedInducedFiltrationStatement` on `GL₄(ℝ)`.

The module is derived from the Library's concrete zero-weight expansion,
finite-filtration algebra and character-pair theorem. It extends the existing
`RealCharacterInducedWeightZero` construction to arbitrary surrounding lists and
an arbitrary block on the other side. It does not use the Langlands classification
or any composition-factor assertion, and claims no separate literature theorem.
