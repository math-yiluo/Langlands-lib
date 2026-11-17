# Actual augmentation-layer determinant transitions

Let `R` and `A` be commutative rings, with `A` an `R`-algebra and an
augmentation `ε : A →ₐ[R] R`. Put `I = ker ε`. Let `σ` be a finite
index type for a specified basis `b` of the actual cotangent module `I/I²`,
and let `z : σ → A` be specified lifts in `I` of that basis.
The universes of `R`, `A` and `σ` are independent.

This is an internal combination of the actual evaluation equivalence from
`SectionJetHomogeneousLayers`, lift and basis compatibility from
`SectionJetLayerNaturality`, and the polynomial determinant formula from
`HomogeneousPolynomialDeterminant`. It adds no external source claim.

`linearForm_basis_repr` proves that the linear forms used for cotangent
basis substitution are exactly the column polynomials of
`b.toMatrix b'`. Its proof expands the finite linear combination and uses
the scalar action on multivariate polynomials.
`cotangentBasisChange_eq_action` consequently identifies the earlier
homogeneous change-of-basis map with the explicit homogeneous polynomial
matrix action. These two results do not require formal smoothness.

Assume that `A` is formally smooth over `R`.
`layerBasis z b hz hzb n` is the basis of the actual module

`Layer ε n = ker (A/I^(n+2) → A/I^(n+1))`

obtained by evaluating degree-`n+1` homogeneous monomials in the chosen
lifts `z`. Its index type is the actual type of natural exponent vectors
of total degree `n+1`. The construction transports the polynomial monomial
basis through `homogeneousEquivLayer`.

For a second basis `b'` with the same finite index type and arbitrary
lifts `z'`, `layerBasis_toMatrix` identifies the actual basis-transition
matrix with

`HomogeneousPolynomial.representation (b.toMatrix b') (n+1)`.

The implemented proof applies the actual layer compatibility under
cotangent-basis substitution to each monomial vector. After transporting
back through the first evaluation equivalence, the matrix coefficient is
exactly the polynomial representation coefficient.

`layerBasis_toMatrix_det` then proves that the determinant of this actual
layer transition is

`det(b.toMatrix b') ^ HomogeneousPolynomial.exponent σ (n+1)`.

This is a positive natural exponent by `HomogeneousPolynomial.exponent_pos`.
Its convention for the empty variable type is retained; all empty
cotangent transition determinants are one. The results have no field,
domain, noetherian or finite-type hypothesis on the base or algebra.
This module treats two cotangent bases indexed by the same finite type.
It does not yet construct a total-jet determinant comparison, sheaf
gluing, or a comparison with the actual group Lie sheaf.
