# Affine product factorization through tensor equations

This internal derived unit compares the previously constructed affine coefficient
locus with factorization of an actual affine fibre product through a closed
subscheme defined by an ideal I of A tensor_R C. The right factor C is projective
over R, without a finite generation condition. The coefficient map f:A to B is
arbitrary; B need not be flat.

The generic `affine_factorsThrough_quotient_iff` reduces factorization through an
ideal quotient to the ring-kernel criterion, using global-sections/spectrum
naturality and invariance of kernels under an invertible target map.
`affine_coefficientLocus_iff_tensorQuotient` then combines the coefficient-ideal
criterion with the same quotient criterion for the tensor-algebra map.

`affineProductMap` transports Spec(f tensor id_C) through Mathlib's
`pullbackSpecIso`. Its two projection identities identify it as the actual
product map Spec(f) times id_Spec(C). `affineTensorQuotientι` places the original
tensor-ideal quotient inside the actual fibre product and is a closed immersion.
Finally `affine_coefficientLocus_iff_productFactorization` transports both
factorizations through these canonical isomorphisms. Its conclusion quantifies
over every R-algebra B and f:A to B.

This implements the affine-test product comparison in the coefficient argument
of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Proposition A.8.10(1), printed pp. 547–549. The product is written with the
coefficient scheme Spec A first and the projective coordinate scheme Spec C
second. Arbitrary-test locality, gluing over a nonaffine coefficient scheme,
faithfully flat descent, and all three group-scheme representability targets
remain separate obligations.
