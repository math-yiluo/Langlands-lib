# Invariant polynomials from linear matrices

This internal construction implements the final determinant step in the route
to Haboush's theorem. It does not prove the existence of the required linear
map, or geometric reductivity of a reductive group.

For coefficient matrices \(c_a\), `MatrixLinear.polynomial` has entries
\(\sum_a (c_a)_{ij}X_a\), and `MatrixLinear.determinant` is its determinant.
The determinant is homogeneous of degree equal to the number of matrix rows.
`MatrixLinear.eval_determinant` proves that evaluation through any ring
homomorphism commutes with this construction. Both facts hold over an
arbitrary commutative coefficient ring.

For actual coordinate representations `ρ` and `σ` of a group scheme,
`MatrixRepresentation.ConjugationLinearMap ρ σ` supplies these coefficient
matrices together with equivariance for conjugation by `σ`. The equivariance
condition quantifies every test scheme, every group point on it, and every
vector with entries in its ring of global sections. Thus it gives the same
scheme-theoretic invariance scope as the existing Haboush target.

If the matrix at a vector `v` has nonzero determinant, and the matrix index
type is nonempty, `exists_invariant_polynomial` produces the required
positive-degree homogeneous invariant polynomial with nonzero value at `v`.
It uses `RingHom.map_det` for arbitrary scalar evaluation and
`Matrix.det_units_conj` for invariance. The homogeneity proof expands the
determinant into signed products of degree-one linear polynomials.

The construction is derived algebra rather than a new external theorem.
Its intended application follows D. Mumford, J. Fogarty and F. Kirwan,
*Geometric Invariant Theory*, third enlarged edition (1994), Appendix 1.A,
printed p.192, the proof sketch of Theorem A.1.0 a) implies b)
(registered source `mumford-fogarty-kirwan-1994-git-3rd`). That sketch obtains
a map into the endomorphisms of a Steinberg module and applies determinant.
The present module proves only the determinant step. In particular, the
Steinberg module, the required map and reductive-group reductions remain
separate substantive obligations.
