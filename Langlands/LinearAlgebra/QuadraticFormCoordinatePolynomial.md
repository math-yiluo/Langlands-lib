# Coordinate polynomials and finite-field anisotropic quadratic dimension

This internal construction represents an actual quadratic form by a polynomial
of total degree at most two. It permits every field characteristic, including
two, and independent field, vector-space and finite-index universes.

For a finite family of vectors `b`, `coordinatePolynomial Q b` contains the
diagonal terms `Q (b i) * X i ^ 2` and one cross term for each unordered
distinct pair of indices. The cross coefficient is the quadratic polar
pairing `Q (b i + b j) - Q (b i) - Q (b j)`. Its symmetry makes `crossTerm`
well-defined on `Sym2`. The published quadratic-map finite-sum formula proves
that evaluating this polynomial at `x` gives `Q (∑ i, x i • b i)`. Each term
has degree at most two, and the finite sums retain this bound.

The theorem `finiteField_finrank_le_two` applies this construction to a finite
basis over a finite field. If `Q` is anisotropic, its coordinate polynomial
has exactly one zero, the origin. If the vector-space dimension exceeded two,
Mathlib's `char_dvd_card_solutions` would make the field
characteristic divide that number of zeros. A prime cannot divide one, so
the dimension is at most two. The argument applies to singular forms in
characteristic two as well.

The provenance is an internal consequence of Mathlib's quadratic finite-sum,
polynomial degree and Chevalley–Warning results. No local-field residue
lattice or local quadratic dimension bound is proved here. This finite-field
result is a possible input to the separate local arithmetic proof.
