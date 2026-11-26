# The degree-one polynomial in the Harris–Taylor projector

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p. 98 (PDF p. 106), defines the
operator \(\epsilon(m)\) on the cohomology of the \(m\)-fold power
of the tautological abelian scheme. Its \(x\)-th factor is

\[
 f_D([2]_x^*), \qquad
 f_D(T)=\prod_{\substack{0\le j\le D\\j\ne 1}}
              \frac{T-2^j}{2-2^j},
 \qquad D=2dn^2.
\]

Here the \(d\) on the right in the source's \(2dn^2\) is the
degree of the totally real field. The code takes the full bound
as its argument. The registered book is
`harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

`degreeOnePolynomial` is this polynomial over a field, and
`degreeOneEndomorphism` evaluates it at each of a finite tuple of
elements of an algebra over that field. The products of evaluated
factors are ordered by the tuple indices. The empty tuple gives the
identity. For actual cohomology, these elements are the pullbacks by
the factorwise multiplication-by-two maps. The ambient endomorphism
algebra can also be the algebra of endomorphisms of a module.

Over a characteristic-zero field, each denominator is nonzero
because the powers of \(2\) in the natural numbers are distinct.
`degreeOnePolynomial_eval_two` gives \(f_D(2)=1\).
`degreeOnePolynomial_eval_pow` gives \(f_D(2^j)=0\) for the other
powers in the prescribed range. A product of linear endomorphisms
on a simultaneous eigenvector acts by the product of their
eigenvalues. `degreeOneEndomorphism_apply_of_eigenvectors` therefore
gives the action stated in the source on a summand indexed by the
degrees of the factors. `degreeOneEndomorphism_idempotent` proves
idempotence when those simultaneous eigenspaces span the module.
For the geometric application, the cohomology of the relative power
must supply this eigenspace spanning. The representation-theoretic
projector \(\epsilon_\xi\) and the Tate twist are additional parts of
the coefficient construction.
