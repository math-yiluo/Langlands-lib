# Pullback of an actual split polarized affine point

`SplitPDivisibleAffinePoint.baseChange` extends the target formal module
along an affine test map `T → U`. Its primal rigidifier is the pullback
of the old primal rigidifier along the induced map `T/(π) → U/(π)`.
The two natural tower comparisons place it between the new frame and
target over `U/(π)`.

For the source, the map from the frame's residue field factors through
`T/(π)`. For the target, the coefficient comparison identifies the tower
of the extended formal module with the pullback of the original tower.
The commuting reduction square then identifies reduction of this
pullback with pullback of the original reduction. These comparisons
are order-linear. The target remains square-height special, and the
common `ℚ_p` multiplier is unchanged. Applying `rigidifier` to this
point gives the corresponding full split special-fibre rigidifier.

This is the pointwise change of test for the split affine presentation
of C1 in Harris (1997), Appendix, printed p. 113 (PDF p. 39), conditions
(i)–(iii). Compare Rapoport–Zink (1996), Definition 2.15, printed p. 54
(PDF p. 69), for the pullback in the framed deformation problem.
