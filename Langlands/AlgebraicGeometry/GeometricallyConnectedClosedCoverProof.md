# Proof of the finite closed-cover geometric connectedness criterion

The theorem `finiteClosedGeometricallyConnectedCoverCriterion` proves exactly
`FiniteClosedGeometricallyConnectedCoverCriterion`, with independent scheme and
field universe `u` and index universe `v`. The statement retains the original
actual schemes and morphisms and has no finite-type or Noetherian hypothesis.

For the forward implication, a geometrically connected morphism to the spectrum
of a field has connected source. Every covering piece also has connected,
nonempty source. The ranges of the closed immersions are closed and nonempty;
they cover the whole source. The imported finite closed-cover theorem therefore
makes their actual intersection relation chain connected. Its inhabited-index
conclusion also handles the empty-family case correctly.

For the reverse implication, consider an arbitrary morphism from the spectrum
of a field `L` to the spectrum of the original field. The actual pullback
projection is surjective. Its base-changed covering ranges cover the pullback,
and surjectivity identifies their pairwise nonempty intersections with those
of the original ranges. The imported comparison therefore transports the
finite-chain condition. Each base-changed range is closed because closed
immersions are stable under scheme base change.

Each piece remains connected on this pullback. The helper
`isConnected_fieldBaseChangeSubschemeRanges` identifies the nested pullback
`Z i ×[X] (X ×[Spec K] Spec L)` with
`Z i ×[Spec K] Spec L` by Mathlib's actual pullback-pasting isomorphism.
Geometric connectedness of `Z i ⟶ Spec K` makes the latter connected. The
homeomorphism transfers this to the nested pullback, and the continuous image
under its projection is the actual covering range, which is therefore
connected. The finite closed connected-cover theorem now gives connectedness
of the whole pullback. Testing every field-spectrum morphism proves geometric
connectedness of the original morphism.

This implements the fixed-fibre intersection argument isolated from Stacks
Project Lemma 37.28.4 (055G), final paragraph of the proof, in the registered
source `stacks-fibre-constructibility-local-dimension-2026-11-04`, retained
`055C.html`. The original paragraph uses geometrically irreducible pieces;
this derived criterion uses only geometric connectedness. The proof does not require the pieces to be maximal
irreducible components and tests arbitrary field extensions, with no finite,
separability or algebraicity restriction. It proves no existence or spreading
of the covering pieces; those and the general generic-constancy theorem remain
separate obligations.


The Lean proof was supplied by Worker 105 and reused unchanged by Worker 1437,
who checked it against the published statement and helper modules.
