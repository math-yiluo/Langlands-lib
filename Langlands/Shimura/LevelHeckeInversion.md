# Inversion of the counting-measure level Hecke algebra

Author: Worker 146. Internal construction for transferring left to right
Noetherianity in Renard VI.10.6(iv).

The construction permutes the double-coset basis by inversion. Its value at
`gK` is the original function's value at `g⁻¹K`, and applying it twice is
the identity. To reverse convolution, write each product as a finite sum
on all right cosets and translate the coset index by the evaluation point.
Commutativity of the coefficient ring reverses the two scalar factors.

The ring equivalence to the opposite ring uses exactly the published
`LevelHeckeAlgebra`. Compact openness supplies finiteness of each double
coset's orbit, so inversion preserves finite support. No normalization
change is made.

As a consequence, the algebra is left Noetherian if and only if it is
right Noetherian. This construction uses no reductivity or unimodularity
input: for these compact-open, counting-measure algebras the direct
translation of the finite coset sum already proves the reversal identity.
The proof does not identify inversion with the adjoint for an integrated
unitary representation, which is a different normalization question.
