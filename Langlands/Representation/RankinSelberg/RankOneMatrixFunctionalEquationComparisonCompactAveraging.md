# Actual compact averaging in the unchanged coefficient model

This derived prerequisite uses the compact corner kernel to construct an actual
right average of the supplied Whittaker vector. In positive rank write
`y=(a,k)` and set `U(y,v)=(1+v E_01) diag((product a)^(-1),a) k`.
The matrix identity
`diag(t,1,...) U(y,v)=(1+t v E_01) diag(t/product a,a) k`
introduces precisely the standard-character factor `psi(t v)`. Every such
translate has normalized determinant absolute value one for integral `k`.

The parameter measure is the actual Iwasawa tail density times Haar restricted
to the integral subgroup, followed by the unchanged supplied scalar Haar
measure. It is finite on compact sets. One jointly compact Schwartz kernel,
chosen from the supplied matrix test, therefore gives a scalar-integrable right
average of every input vector in its original coefficient model. Algebraic
smooth averaging constructs the averaged vector without placing a topology on
the representation carrier. Fubini applies because the weighted orbit is
actually integrable on the parameter product. Scalar Fourier reconstruction
then identifies its restriction to the embedded rank-one group with the
parameter integral of the original unipotent transform times the original
model function.

The averaging kernel is independent of the input vector. The construction
keeps the original functional, model, nontrivial character and self-dual scalar
measure, with independent field and representation universes. It treats
positive rank; it does not supply weighted integrability in the rank-one
variable, a dual matrix identity, or the final paired gamma comparison.
