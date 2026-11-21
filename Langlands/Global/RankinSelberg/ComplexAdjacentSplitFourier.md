# Fourier transforms of the split Godement test

`complexAdjacentSplitFourier` identifies the positive-phase rectangular
Fourier transform of a split Godement test with the product of its
positive-phase square and column transforms. The square factor is the
Library's negative-phase matrix transform evaluated at the negative
matrix. The column factor is `splitRowTransform a φ`, a Schwartz
representative of the positive-phase transform. Applying the
opposite-phase row integral to this factor recovers the original
column test pointwise.

The proof factors the rectangular Fourier integral by separating the
last column. It compares the coordinatewise square pairing with the
trace used by `matrixTransform` and applies Fourier inversion on the
finite product of complex lines with the self-dual product measure.

These identities give the test-function substitutions in equation
(8.4) of Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*, 2009,
DOI `10.1090/conm/489/09547`.
