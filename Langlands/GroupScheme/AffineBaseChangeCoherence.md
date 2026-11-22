# Composition comparisons for affine pullback of commutative group schemes

`CommGroupScheme.baseChangeCompAlong` lifts the scheme pullback composition
isomorphism to commutative group schemes. Its inputs are two composable
scheme maps and a chosen expression for their composite with an equality.
`CommGroupScheme.affineBaseChangeCompNatIso` specializes this comparison to
spectra of a scalar tower `R → S → T`. The equality between the spectral
maps follows from the scalar tower equation. Naturality follows from the
scheme pullback comparison lifted to group objects. The natural isomorphism
points from direct pullback to successive pullback.

This derived construction supplies a common comparison for the finite
Cartier dual and the finite levels of a p-divisible group. It supports
pullback of the split polarized product in Rapoport–Zink (1996), §6.43,
printed p. 309 (PDF p. 321), preceding (6.17).
