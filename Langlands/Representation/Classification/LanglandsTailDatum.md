# Ordered tails of tempered Langlands data

Author: Worker 111.

This is an internal restriction construction from the published
`Classification.LanglandsData` and `Group.GL.HeadTailBlocks` modules.
It introduces no classification or analytic theorem.

For a genuine tempered Langlands datum `d` with `k + 2` blocks,
`TemperedLanglandsDatum.tail d h` has the published tail shape, whose rank
is the sum of the original sizes after the first block. This rank is positive
by `BlockShape.tailRank_pos`. Its blocks and exponents are the original ones
at `BlockShape.tailIndex h j`, in their original order. The field universe
`uF` and block carrier universe `uV` remain independent.

Irreducibility and analytic temperedness are inherited directly from the
corresponding fields of `d`. Strict decrease of the restricted exponents follows
by composing `d.strictAnti` with the published strictly increasing tail-label
map. No representation transport or new temperedness proof is required:
the tail block sizes are definitionally the original sizes at those labels.

The component formulas and `tail_twistedBlocks` are definitional equalities.
`tail_standardModule` identifies the bundled tail standard module with the
actual normalized product of the remaining original twisted blocks, without
an additional carrier lift. It too is a definitional equality, using the
published definitions of `standardModule`, `twistedProductInduced` and
`twistedBlocks`. This identifies the tail object needed when applying a
first-block and tail regrouping equivalence; this module does not construct
that equivalence.

`tail_length_lt` proves that the restriction has fewer blocks, and
`tail_exponent_lt_head` applies the original strict decrease to the fact that
the first label precedes every tail label. These are the combinatorial facts
needed to use the datum in induction on the number of blocks.

The construction asserts no Whittaker type, L-polynomial existence,
divisibility or product law. Those remain separate obligations of the
Langlands-type L-factor proof.
