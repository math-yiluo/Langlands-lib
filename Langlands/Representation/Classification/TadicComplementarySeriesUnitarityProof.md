# Complementary-series unitarity on an open interval: proof

Authors: Worker 607 and Worker 84.

This module implements the open-interval clause of
`Langlands.Classification.ComplementarySeriesUnitarity` as
`complementaryProduct_unitarizableOnInterval`. Its theorem
`complementarySeriesOpenIntervalUnitarity` proves the focused proposition
`Langlands.Classification.ComplementarySeriesOpenIntervalUnitarity.{uF, uV} F T`.
It does not prove the
all-constituent endpoint clause or the complete target.

For the actual uniform two-block family, irreducibility of the inducing
representation gives admissibility by the published cuspidal embedding theorem.
The published exponent-height construction realizes all real twists on the
untwisted normalized induced function space. Its compact-subgroup action is
constant and all scalar matrix coefficients are continuous. The actual compact
integral of the tensor positive form pairs the members at opposite parameters.
The published irreducible two-factor swap, transported to the uniform block
shape by `JuxtaposedShuffle.uniform_two_swap_of_isIrreducible'`, identifies
these two members. Composing this equivalence with the compact integral pairing
gives a nonzero invariant sesquilinear form for each irreducible member. The
published `unitarizabilityContinuation` then propagates the positive form at
zero across the preconnected open interval.

This is a derived proof using the published construction in
`Classification/ExponentFamily` and the argument already implemented for
supercuspidal blocks in `Classification/TwoSupercuspidalAdjacentReducibilityProof`.
The compact construction and its pairing require only unitary blocks; the
special supercuspidal irreducibility and large-exponent assertions from that
proof are not used here. The mathematical target is Tadic 1986,
`tadic-1986-unitary`, Proposition 2.9, printed p.350 (one-based PDF p.17).
The continuation route expands the soft unitarity step also used in
Zelevinsky 1980, `zelevinsky-1980-induced-ii`, Proposition 1.11, printed p.175.

The family-to-product comparison first identifies the exponent vectors
`s * (1, -1)` and `(s, -s)`, then transports the representation equivalence
through that equality. Its existence is packaged as a `Nonempty` theorem.
The proof uses an invariant positive definite form at zero and a nonzero
invariant sesquilinear form at every irreducible member, precisely the inputs
of the published continuation theorem.

The field and representation universes remain independent, with carriers in
`max uF uV`, as in the full target. The endpoint assertion needs a separate
argument for every irreducible actual subquotient and is not a conclusion of
this proof.
