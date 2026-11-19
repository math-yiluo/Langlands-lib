# The adjacent filtration for two induction blocks on GL₄(ℝ)

`Langlands.Archimedean.realInducedInducedFiltration` proves the Library
proposition `Langlands.Archimedean.RealInducedInducedFiltrationStatement`.
For all complex-character data `d` and `e` in strictly ascending real
exponent order, it gives `RealAdjacentFiltration 4 [] [] (.induced d)
(.induced e)` on the actual right `O(4)`-finite standard module. The source
of each map is the exchanged pair or a standard module with permuted
exponent support and strictly larger squared weight sum. The maps
intertwine modulo earlier ranges, and their ranges span the target.

When either original weight is zero, the proof applies the corresponding
left or right zero-weight theorem. Those constructions expand the
weight-zero block into two real characters, put the character–induction
filtrations in the ambient module by induction in stages, and fuse them
back. The left zero-weight theorem also covers simultaneous vanishing.
For two nonzero weights with no linked index, the unlinked theorem obtains
one piece from the exact swap intertwiner. The two orders have the same
compact type multiplicities, so its injectivity gives surjectivity.

For a linked index `k`, the proof compares the signed inner weight with
zero. Each of the three signs uses a filtration on the same original
two-block module.

- For a negative inner weight, the compact polynomial braid yields an
  identity among the specialized crossing operators. It makes the mixed
  map vanish on the kernel of the replacement quotient. Quotient descent
  gives a map from the replacement pair, and its range and the exchanged
  range give the two pieces. The polynomial braid used here is proved via
  the corner factorizations and interpolation in a Laurent extension and
  then applied to the finite compact rotation endomorphisms.
- At zero inner weight, the zero-difference swap is a generic multiplier.
  The ascending word and its surjective suffix give two pieces from the
  exchanged pair and the outer fused block with its two unused endpoints.
- For a positive inner weight, the crossed-quotient kernel is the sum of
  the two outer parity prefixes. The proof of containment in the sum
  splits the section in the flipped presentation into two low-window
  terms, lifts each into the middle tail kernel, and compares the signed
  high coefficients of the actual pair quotients. The two-prefix
  construction gives five pieces, ending with the crossed pair.

The proof derives the filtration independently of the Langlands
classification and composition-series theorems. The successive quotients are
presented by the intertwining source maps in `RealAdjacentFiltration`.
