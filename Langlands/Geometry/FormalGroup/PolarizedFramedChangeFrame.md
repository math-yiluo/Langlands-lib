# Changing the residue frame of the affine polarized functor

For a rational similitude \(g\) from one fixed residue frame to
another, `changeFrame` sends an affine triple \((X,\rho,\lambda)\)
to \((X,\rho\circ g^{-1},\lambda)\). Here \(g^{-1}\) is its actual
inverse section after extension to the test residue algebra.
For original multiplier \(c\) and frame multiplier \(d\), the
new framing has multiplier \(d^{-1}c\).

Integral polarized isometries of triples still intertwine the
new framing maps. The operation therefore descends to classes.
Naturality follows from the residue coefficient square and the
composite pullback law for rational sections. It uses the
identity coordinate series of the two source comparisons.
The inverse frame change gives the inverse transformation, so
`changeFrameNatIso` is a natural isomorphism of the affine
polarized class functors.

On automorphisms of one frame this is the inverse-precomposition
formula in Harris (1997), Appendix, printed p. 113 (PDF p. 39).
The argument uses the actual section isomorphism and both of
its pairing certificates. A specific relative Frobenius needs
these certificates to instantiate the construction.
