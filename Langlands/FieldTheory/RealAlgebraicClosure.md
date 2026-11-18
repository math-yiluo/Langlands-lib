# Algebraic closures of fields isomorphic to the real numbers

`Langlands.FieldTheory.RealAlgebraicClosureStatement` gives two properties
of the algebraic closure of a field `K` isomorphic to `ℝ`. It has dimension
two over `K`, and every commutative `K`-algebra containing a square root of
`-1` admits a `K`-algebra homomorphism from it. The algebra may be in a
different universe from `K`.

Transport the real scalar action on `ℂ` to `K` and embed the algebraic closure
of `K` in `ℂ`. The image contains the real axis and contains `I`, since a
square root of `-1` in the source maps to `I` or `-I`. The embedding is
therefore surjective. The dimension computation transports Mathlib's
`Complex.finrank_real_complex` along this isomorphism.

Over `K`, the polynomial `X² + 1` is irreducible. A root in `K` would map
to a real number whose square is negative. Its root algebra maps into the
algebraic closure by choosing a root there. Both fields have dimension two,
so that map is an isomorphism. Evaluating the root at any square root of
`-1` in the target algebra gives the required homomorphism.

The auxiliary theorem `exists_sq_eq_neg_one_splittingField` obtains a root
of the same degree-two polynomial in its splitting field over any field.
