# One-sided lifting on an ambient compact degree layer

`RealAmbientAdjacentLiftingStatement` applies to polynomial functions of
degree at most `D` on `O(n)` and the two rotations on consecutive pairs
in an embedded three-coordinate block. Either rotation can be the primary
one. For a positive integer `N`, suppose the degree-`H` differential tail
polynomial in the normalized adjacent generator sends `v` to a function
whose primary Fourier projections at indices `j ≥ N+H` all vanish. The
degree layer then contains a vector in the polynomial kernel with the same
primary projections as `v` at every `j ≥ N`.

The proof transfers the rotation operators in `RealOrthogonalUncertainty`
to the ambient compact group. Restricting to a right coset of the embedded
`O(3)` preserves the degree bound. Right translation preserves the ambient
linear span of the matrix entries and constants. The block embedding pulls
each entry back to a local entry or a constant, so the corresponding
algebra maps preserve all powers of the degree-one spans.

For a local linear operator, apply it to the restriction of an ambient
function on each coset and evaluate at the identity of `O(3)`. On the
finite-dimensional local degree layer this evaluation after the operator
is a finite linear combination of point evaluations. Consequently the
ambient function is a finite linear combination of left translates by
embedded compact elements and has degree at most `D`. The local Fourier
projections commute with right translation since the rotations act on the
left. The same holds for the generators, which are weighted sums of those
projections. This commutation makes the ambient operators agree with the
local operators on the whole coset.

The coset restrictions determine the ambient function, as evaluation at
the identity gives its value at the coset representative. The local mode
decomposition and commutator identities therefore give the corresponding
ambient identities. `RealAdjacentRotationLifting` now gives the lift in
the same degree layer. On restrictions of functions on `GL_n(ℝ)`, the
transferred projections equal the left block Fourier coefficients divided
by `2π`. In particular, a Fourier polynomial identity on compact values
gives the corresponding operator identity on the ambient degree layer
by summing its projections.
