# Analytic compact-picture orbits of the real Frobenius functions

The local Iwasawa map at the identity is real analytic, and its invertible
derivative is the linear splitting into upper triangular and skew-symmetric
parts. The analytic inverse function theorem gives triangular and orthogonal
factors of matrices close to the identity. The diagonal character is real
analytic there because its diagonal entries are positive, so its sign factors
are locally constant and the complex powers use the positive real branch.

For a Frobenius function whose compact coefficient is an entry polynomial,
the compact profile of a right translate has a supremum-norm analytic germ
near the identity matrix. For each orthogonal matrix \(k\), the proof factors
\(k g k^{-1}\) locally and multiplies its orthogonal factor by \(k\). The
pointwise lifting theorem for continuous functions on a compact space supplies
one neighborhood on which these formulas hold for every \(k\). Evaluating the
entry polynomial in the algebra of continuous functions and multiplying by the
lifted diagonal character gives the profile.

This internal result uses the Frobenius formula and local coordinates in
`RealJacquetFrobeniusProof`, together with the pointwise lift in
`CompactMapAnalytic`.
