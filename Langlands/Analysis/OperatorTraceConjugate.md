# Conjugation by a conjugate-linear Hilbert isometry

For a conjugate-linear isometric equivalence \(e:H\to J\) of complex
Hilbert spaces, `conjugateHilbertOperator e T` is the bounded complex-linear
operator \(eTe^{-1}\). Suppose \(e\) takes the original inner product to
its complex conjugate. Its image of a Hilbert basis is then orthonormal
with trivial orthogonal complement, so it gives a Hilbert basis of \(J\).

The image basis preserves all squared norms in the Hilbert–Schmidt sum.
The two-factor Hilbert–Schmidt characterization of trace class then shows
that \(eTe^{-1}\) is trace class when \(T\) is trace class. The image basis
conjugates each complex diagonal entry, and complex conjugation commutes
with its sum, giving
\(\operatorname{tr}(eTe^{-1})=\overline{\operatorname{tr}(T)}\).

This is an internal consequence of the Hilbert–Schmidt and operator trace
laws for the continuous dual calculation.
