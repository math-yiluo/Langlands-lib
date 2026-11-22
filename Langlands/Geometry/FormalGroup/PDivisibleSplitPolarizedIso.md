# Isomorphisms of actual split polarized towers

Over an affine base, `splitPolarizedIso` takes an integral isomorphism
`e` of the primal towers and a proof of
`FiniteCartierDualExactnessStatement`. The proof supplies the reversed
short exact sequences that form the actual Cartier dual towers. The
split isomorphism has blocks `e` and `(e⁻¹)∨`. It preserves identity and
composition and commutes with the actual product and Cartier comparisons
under affine base change.

The dual block composes with the dual of the primal block to give the
identity. This proves strict preservation of the alternating pairing
on every finite level and test. The rational map has multiplier one.
If the primal isomorphism intertwines the order actions, rational
order-linearity and faithfulness give the same equation for the
integral split map.

Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), gives the
split polarized form of the target before (6.17). Harris (1997),
Appendix, printed p. 113 (PDF p. 39), uses polarized isomorphism classes
in C1. The Lean construction supplies integral isometries for that
split presentation.
