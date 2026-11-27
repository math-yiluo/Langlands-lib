# The degree-one selector on an abelian power

`RelativePowerDegreeOneProjectorStatement` applies the normalized
multiplication-by-two selector of Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), III.2, printed p. 98
(PDF p. 106), to the actual relative power of an abelian scheme. The base
`S` is proper over an algebraically closed field, `p` is invertible on
`S`, and the dimensions of its geometric abelian fibres are bounded by
`g`. The `m`th power has its actual relative structure map and each
factor map multiplies by two on that factor. The polynomial bound is
`2*g`, which specializes to the source bound `2*d*n²` for the universal
family of that dimension. The zeroth power is `S`, with the empty
product of operators equal to the identity.

The two groups on which the same polynomial is evaluated are the
rationalizations of the inverse limits of the following finite-stage
groups, where `π` is the structure map of the power.

- `H^i(S, R^j π_* ℤ_p/(p)^r)`, using the relative pullback on the actual
  higher direct images for the factor maps.
- `H^q(A^m, ℤ_p/(p)^r)`, using the actual geometric global pullbacks.

The proposition asserts that the resulting operators are idempotent,
that the relative-image operator vanishes for `j ≠ m`, and that the
linear images at `(i,m)` and `i+m` are isomorphic. The last clause
asserts existence of the linear isomorphism. The representation-theoretic
idempotent, the Tate twist and the identification with the algebraic
coefficient system are further comparisons.

The relative Künneth summands are indexed by factor degrees with sum `j`.
The action of the `x`th factor operator on each such summand is the
scalar `2` raised to the `x`th factor degree. This explains the degree
selected by the polynomial. In the finite decreasing Leray filtration
of total cohomology in degree `q`, the product of the factor multiplications
acts by `2^j` on the associated graded piece of relative degree `j`.
These eigenvalues are distinct for distinct filtration degrees, so the
product separates the graded pieces. Each factor operator commutes with
this product and has the Künneth action on its eigenspaces. Projecting to
the all-degree-one summand identifies the selected Leray term with the
selected total group. Proper finiteness at the finite stages gives
exactness of the inverse limits used in passing to these rational groups.

The source uses the same polynomial on the universal abelian powers, and
then uses the Leray sequence to identify the coefficient contribution.
Its retained edition has literature ID
`harris-taylor-2001-geometry-cohomology-simple-shimura` and SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The Künneth and Leray comparisons are Milne 1980, VI.8.5 and III.1.18(a).
