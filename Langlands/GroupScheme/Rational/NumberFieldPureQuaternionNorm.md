# Local-to-global representation by the norm of pure quaternions

`Langlands.GroupScheme.Quaternionic.FirstKindInvolution.NumberFieldPureQuaternionNormStatement` says that the reduced norm of the pure quaternion subspace represents a scalar over a number field if it represents that scalar at every completion. Purity is membership in the alternating subspace of the actual quaternion conjugation. At a completion both the algebra and the conjugation are extended to the entire tensor algebra. `numberFieldPureQuaternionNorm` proves the statement for every universe.

Compose the conjugate-product pairing with a linear retraction of the scalar inclusion and restrict it to the alternating subspace. The resulting quadratic form equals the reduced norm there. The division algebra has no zero divisors, so the form is anisotropic and its polar form is nondegenerate in characteristic zero. Scalar extension of the alternating subspace is the alternating subspace of the extended conjugation, and the extended conjugate product still equals the reduced norm. The local representations thus supply the hypotheses of `numberFieldQuadraticRepresentation`.

This formalizes the pure-quaternion norm step used in the proof of Theorem 5.3.3 of T. A. Springer's appendix to Kneser, *Lectures on Galois Cohomology of Classical Groups*, printed pp. 109–110 (PDF pp. 115–116).
