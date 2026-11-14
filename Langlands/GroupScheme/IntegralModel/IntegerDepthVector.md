# Integer-depth vector models over a valuation ring

This internal construction supplies explicit integral vector models for a field
with a surjective valuation into `WithZero (Multiplicative ℤ)`. The coefficient
ring is any valuation subring equal to the supplied valuation's ring, so it can
be an already fixed integral subring of the same field. No completeness or
Henselian hypothesis is required.

At integer depth `m`, choose a nonzero scalar whose multiplicative value is
`exp(-m)`. At real depth `r`, use the scaled polynomial vector model with scalar
at `ceil(r)`. Its actual integral-point image consists exactly of vectors whose
coordinate values are at most `exp(-ceil(r))`. The underlying model is the
standard smooth vector group with geometrically connected fibres. All finite
dimensions, including zero, are allowed.

For `r ≤ s`, the quotient of the depth-`s` scalar by the depth-`r` scalar is
integral. Multiplication by this quotient defines a model map from depth `s` to
depth `r`, extending the generic identity. Every compatible extension has a
smooth, connected and unipotent scheme-theoretic special-fibre kernel.

The proof first shows that the principal lattice consists exactly of the vectors
bounded by the scalar's valuation: division by the nonzero scalar produces the
integral coefficients. The existing exact integral-point computation then gives
the coordinate ball. Monotonicity of the ceiling function proves integrality of
the scale quotient. The transition and its kernel properties follow from the
scaled-vector construction and generic rigidity.

The additive integral models in Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023), Section C.2, printed pp.697–698 / PDF pp.728–729, motivate the
construction. The finite-dimensional valuation-ring generality and the
real-depth rounding are derived here. This module does not identify these
coordinate balls with a supplied Bruhat–Tits root filtration; that comparison
remains an obligation in the root-depth kernel theorem.
