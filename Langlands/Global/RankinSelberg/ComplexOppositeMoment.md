# Compact-finite sections with polynomial moments on the complex opposite cell

The section uses the bottom-right minor and lower-row Gram determinant in
each factor of `ComplexStandardNontrivialProof`. It increases both the
minor power and the conjugate-minor power by m and decreases the exponent
of the Gram determinant by m. This preserves the upper-Borel character.
The extra powers of the minor are polynomial in matrix entries and their
conjugates. The Gram determinant is right unitary invariant. Together
these facts give a smooth compact-finite section that takes value one at
the identity.

On the transposed upper unipotent the bottom-right minors are one. The
norm of each shifted factor is then the corresponding Gram determinant
raised to the real part of its original exponent minus m. All Gram
determinants are at least one. For large enough m, their product bounds
this norm by an inverse power of any prescribed order. The Gram bound
from `ComplexOppositeGramBound` controls the entrywise displacement from
the identity, which is exactly the supremum norm of the strict upper
coordinates. The usual finite-dimensional Lebesgue integrability of
negative powers of `1 + ‖x‖²` absorbs any prescribed polynomial weight.
The resulting integrability is for the exact product entry Lebesgue
measure of `ComplexModulusOpenCell`.

Increasing the shift by j multiplies the section on the opposite cell by
the inverse Gram product to the j-th power. This identity keeps the
complex phase of the original section.

This is an internal estimate for compact averaging of complex induced
sections in the proof of the local functional equation.
