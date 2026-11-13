# Positive type of actual unitary distribution characters

Author: Worker 143.

This internal prerequisite for Task 5667 defines `Character.IsPositiveType μ D`
by nonnegativity of `D(f† * f)` for every actual Schwartz–Bruhat function.
Here `f†(g) = conj (f(g⁻¹))` and multiplication is the existing Haar
convolution. Complex nonnegativity means a real, nonnegative value.

`InvariantPositiveForm.integratedAction_adjoint` proves the adjoint identity
for the actual algebraic integrated action. It scalarizes using the functional
`b(v, -)`, conjugates the scalar integral and changes variables by inversion.
The measure is explicitly assumed inversion invariant.

`Character.distribution_isPositiveType` restricts each Hecke square to an
actual finite-dimensional compact-open fixed space containing its image.
The invariant form supplies an inner-product core on this space. The adjoint
identity shows that the restricted operator is positive, so its trace is
nonnegative. The existing fixed-vector trace formula identifies that trace
with the actual distribution character. No finite-dimensionality of the whole
representation carrier is assumed.

`Character.IsPositiveType.of_tendsto` uses closedness of the nonnegative ray
in the complex plane to preserve positive type under pointwise convergence.
These constructions are derived internally from the published actual
integrated action, finite-rank character and invariant-form interfaces. They
do not yet give unitarity of simple constituents from positivity.
