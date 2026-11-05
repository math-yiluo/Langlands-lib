# Degree-one invariant separation from semisimple rational-point representations

This derived unit implements the elementary implication from complete reducibility to
geometric reductivity in coordinates. It does not prove complete reducibility for
reductive groups in characteristic zero, and does not prove Haboush's theorem.

For an abstract group representation, `SemisimpleFixedSeparation.exists_invariant_form`
chooses a stable complement to the subspace of fixed vectors. Projection along that
complement is invariant, and composing it with a linear functional taking value one
at the chosen nonzero fixed vector gives an invariant functional with that value.
The coefficient field, group and vector-space universes are independent.

For an actual group-scheme coordinate representation, `rationalRepresentation`
uses the actual rational-point matrices. `linearPolynomial c` is the polynomial
sum of `c i * X i`. It is homogeneous of degree one, and arbitrary-ring evaluation
is the coordinate dot product after scalar extension. A vector fixed by the actual
dual representation therefore yields an invariant polynomial on every test scheme;
the proof uses the inverse-transpose pairing identity for invertible matrices.

For a smooth group over an algebraically closed field,
`isFixedVector_iff_rationalRepresentation` identifies all-test fixedness with
fixedness under this rational-point representation. Its reverse direction uses
reducedness of a smooth scheme over a field and rational-point detection of equality
of morphisms to the separated affine coordinate space, through the Library's
`SchemeAction.isFixed_iff_rationalPoints`. This step extends to all tests, including
nonreduced and nonaffine tests; those tests themselves are not assumed reduced.

The closing construction assumes that the actual rational-point representation
is semisimple. It constructs the invariant functional, identifies its coefficients
as a fixed dual vector, and takes their linear polynomial. The result is homogeneous
of degree one, is invariant on every scheme test, and is nonzero at the chosen
fixed vector; the intermediate dual vector is normalized to pair to one. No reductivity or characteristic assumption is used in this conditional
algebraic bridge. The missing theorem that reductive groups in characteristic zero
have semisimple rational representations remains a separate obligation.

Provenance: Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third enlarged
edition (1994), Appendix to Chapter 1, Section A, printed p.191 (PDF zero-based
index 202), definitions (ii) and (iii) and the implication from linear to geometric
reductivity. Source ID `mumford-fogarty-kirwan-1994-git-3rd`. The implementation uses
the Library's actual representation and dual definitions and Mathlib's complemented
subrepresentation lattice, linear projections, separating dual and homogeneous
polynomial algebra. The source's characteristic-zero equivalence of reductivity
and linear reductivity is not an input silently discharged by this construction.
