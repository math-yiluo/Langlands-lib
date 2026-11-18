# Exact polynomial Fourier relations on a common compact model

This internal construction extracts an exact operator interface from the
proof of `RealPolynomialFourierPropagation`. Fix a rotation position
`p` in rank three, a common polynomial degree bound `N`, and functions
`f,g` whose restrictions to `O(3)` belong to `degreeLE 3 N`. Write
`vf,vg` for these vectors and `a=-i gen(N,p)` for the compact generator
whose eigenvalue at Fourier index `j` is `j`.

For arbitrary complex polynomials `P,Q`, `relation_iff` proves the
equivalence between

`P(j) Fourier_j(f) = Q(j) Fourier_j(g)` at every compact point and index,

and the exact vector equation

`P(a) vf = Q(a) vg`.

The proof uses the existing computation of each Fourier projection of
polynomial evaluation. In the forward direction the two vectors have
identical projections, hence are equal by the finite projection sum.
In the reverse direction project the vector equality, evaluate at a
compact point and cancel the nonzero Fourier normalization `1/(2π)`.
No operator inverse or spectral nonvanishing assumption is needed for
this equivalence.

`exists_common_degree` places any finite family of continuous right
compact-finite rank-three functions in a common model, using the finite
maximum of their individual degree bounds. `ambient_common_degree`
does this after restricting a finite family of ambient functions to a
three-coordinate compact coset.
`ambient_relation` transfers an ambient polynomial Fourier relation at
position `a+r` to the exact generator equation on that coset. It uses the
published compact-block Fourier compatibility and applies to any ambient
rank admitting the triple, including rank four.

The actual-map corollaries are also proved:

- `generic_operator` applies to normalized integral generic Frobenius
  maps on their generic parity class. It gives
  `Pℓ(a) v_output = Pℓ(ε) v_input`, using the exact scalar normalization
  of `RealIntegralGenericPolynomial`.
- `tail_operator` applies to an actual tail with symmetry `(-1)^ℓ` and
  gives `v_output=Pℓ(a) v_input`. The source parity removes off-parity
  coefficients, and the polynomial tail formula handles the others.

`RealCompactPolynomialFourierRelationStatement` asserts the exact
rank-three equivalence for all common degree bounds, functions and
polynomials. `realCompactPolynomialFourierRelation` proves it.

This unit proves no polynomial braid, equality between a chosen interlaced
equivalence and a prescribed word, or filtration kernel-image containment.
The differential-sign hypothesis on `tail_operator` is explicit; a tail
with the other symmetry is not identified with that polynomial operator.
