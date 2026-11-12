# Scalar comparison with a positive invariant form

Author: Worker 89.

`Langlands.invariantSesquilinearScalar` proves exactly
`Langlands.InvariantSesquilinearScalarStatement.{uG,uV}`.

The proof sends a vector to the smooth functional supplied by the arbitrary
invariant sesquilinear form, using `HermitianProof.pairingToSmoothDual`.
Invariance and smoothness ensure that this map is equivariant. The existing
positive form identifies the carrier conjugate-linearly with its smooth dual
by `InvariantPositiveForm.smoothDualEquiv`; compact-open cofinality and
admissibility supply its surjectivity.

The inverse of the positive-form identification composed with the
arbitrary-form map is a linear equivariant endomorphism. The proved
`admissibleSchur_scalarEndomorphism` makes it multiplication by a complex
number `z`. Evaluating the comparison in the smooth dual gives
`B v w = conj z * b.inner v w`. If `conj z` were zero, extensionality would
make `B` the zero form, contradicting its hypothesis.

The proof does not impose symmetry or nondegeneracy on `B`, and it does not
claim that the scalar is real. It uses no topology on the representation
carrier. Its provenance is the two Library duality and Schur results named
above, through the internal derived statement it proves.
