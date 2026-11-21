# Identity and composition of pullback for actual towers

`baseChangeIdNatIso` compares identity pullback with the original
`p`-divisible group. `baseChangeCompNatIso` compares direct pullback
with successive pullback along a compatible tower of algebra maps.
On each finite group scheme these are the canonical group scheme
pullback comparisons. Their naturality for the inclusions gives an
isomorphism of the inclusion diagrams. `isoOfInclusionDiagrams`
constructs the resulting tower isomorphism, including compatibility
with the transfers.

The rational comparisons use the same integral isomorphisms in the
category up to isogeny. Naturality on pure tensors follows from the
ordinary pullback naturality equation. Additivity extends the equation
to every rational morphism.

These are the pullback comparisons for the actual groups and
quasi-isogenies in Harris (1997), Appendix, printed p. 113 (PDF p. 39),
conditions (i)–(iii) of C1, and Rapoport–Zink (1996), Definition 2.15,
printed p. 54 (PDF p. 69). The Lean proof assembles the comparisons from
those of the finite group schemes.
