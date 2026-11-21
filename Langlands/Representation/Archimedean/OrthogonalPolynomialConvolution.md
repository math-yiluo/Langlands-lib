# Finite rank of convolution by an orthogonal entry polynomial

Right convolution with a continuous scalar weight on the orthogonal group
is bounded on its continuous functions with the supremum norm. Bounded
point evaluation takes the Bochner average to the corresponding scalar
convolution integral.

For a polynomial weight \(\phi\), left invariance of Haar measure rewrites
that integral at \(x\) with the kernel \(\phi(x^{-1}k)\). The Library's
separated-variable expansion expresses this kernel as a finite sum of
products of functions of \(x\) and functions of \(k\). The proof applies
span induction to the expansion. For each fixed kernel, it constructs one
finite-dimensional space of continuous output functions that works for
every input. In particular, the range of the convolution operator is
finite-dimensional.

This internal result uses `OrthogonalFinitePolynomial` for the
separated-variable expansion and `OrthogonalGroupAveraging` for the
bounded operator and its integral formula.
