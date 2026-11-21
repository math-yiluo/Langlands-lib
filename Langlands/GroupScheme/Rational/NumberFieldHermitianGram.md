# Local-to-global Hermitian Gram congruence

`NumberFieldHermitianGramCongruenceStatement` takes two nonsingular Hermitian Gram matrices of the same finite size over a separable quadratic field extension of a number field. If they are congruent over the tensor coefficient algebra at every completion of the base field, they are congruent over the quadratic field. `GramCongruentOver` uses the full tensor algebra, including at places where the quadratic extension splits. The congruence convention acts on row vectors.

Choose a nonzero scalar negated by conjugation and use it to scale both Hermitian matrices into antihermitian matrices. The trace-one retraction applied after division by this scalar detects every alternating value. The scalar quadratic forms are regular, commute with base change, and are isometric at every completion by Gram congruence. Hasse–Minkowski gives an isometry over the base field. The antihermitian scalar comparison recovers a linear Gram congruence over the quadratic field, and cancellation of the common nonzero scalar gives the required Hermitian congruence.

The claim is the matrix-algebra case of the local-to-global theorem for Hermitian congruence in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.5, pp. 76–78. The Lean proof takes the scalar quadratic route for this case.
