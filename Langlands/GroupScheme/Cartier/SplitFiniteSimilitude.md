# Similitudes of the alternating finite Cartier pairing

Let \(G,H\) be finite locally free commutative group schemes over the
affine base. Let \(f:G\to H\) act on the primal factor and let
\(g:G^\vee\to H^\vee\) act on the dual factor. If the composite
\(f^\vee\circ g\) equals multiplication by the integer \(k\), the
pullback of the alternating evaluation on \(H\times H^\vee\) is the
\(k\)-th power of the alternating evaluation on \(G\times G^\vee\).
`productWithDualPairing_similitude` proves this for points over any
test scheme.

For each of the two evaluations in the alternating pairing, move
\(f\) into the dual argument by Cartier adjointness. The resulting
composite sends the dual point to its \(k\)-th power, and evaluation
in that argument is the homomorphism `finiteSchemePairingDual`. Taking
the product with the inverse of the other evaluation gives the formula.

This is the integral finite-level calculation for the split polarized
pair in Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), and
the scalar-multiplier condition of Harris (1997), Appendix, printed
p. 113 (PDF p. 39), condition (iii) of C1.
