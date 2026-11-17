# Polynomial Fourier propagation in arbitrary ambient rank

This internal transfer applies the rank-three polynomial multiplier theorem
to any three consecutive coordinates of `GL_n(ℝ)`. If continuous right
`O(n)`-finite functions `f,g` have Fourier coefficients related by `Q(j)` at
one of the two adjacent rotations in this block, a low cutoff `cutoff`
at the other rotation grows by at most `Q.natDegree`.

At each compact right coset, restrict the functions to the published embedded
`GL₃(ℝ)` block. This preserves continuity and right compact finiteness.
Compatibility of both rotation Fourier coefficients with restriction
transfers the hypotheses to rank three. Apply the rank-three result and
evaluate at the identity of that block to obtain the result at the original
compact coset.

`RealAmbientPolynomialFourierPropagationStatement` is this generic
polynomial multiplier assertion for all ambient ranks and both adjacent
orientations; `realAmbientPolynomialFourierPropagation` proves it.
The helper `tail_propagation` applies it to actual ambient `blockFrobMap`
data with positive tail cutoff `ell`, reduced resonant parity and sign
`(-1)^ell`, giving the cutoff bound `cutoff+ell`. The scalar polynomial
identity is used on the source parity class and source coefficients vanish
off parity.

This result does not yet construct the proposed three-tail quotient between
two-induced-block modules, identify a kernel with preceding source ranges,
or prove the unrestricted linked filtration.
