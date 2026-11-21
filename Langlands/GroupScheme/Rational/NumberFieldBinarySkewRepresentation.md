# Binary representation of pure quaternion values

Let `F` be a number field and `D` a central quaternion division algebra with quaternion conjugation obtained from a supplied orthogonal involution. Let `H` be an invertible binary antihermitian Gram matrix and `c` a nonzero element of the alternating subspace. If the scalar-extended row pairing represents `c` over every completion of `F`, then the global row pairing represents `c`.

Adjoin a last diagonal entry `-c`. Every local solution of the value equation extends to an isotropic row with last coordinate one. The rank-three skew isotropy theorem gives a nonzero global row. If its last coordinate is nonzero, left scaling by its inverse produces a row of value `c` in the original binary form. If its last coordinate is zero, the original form has a nonzero isotropic vector. A normalized skew hyperbolic partner then gives a row of value `c` by adding a half-value multiple of the isotropic vector.

This is the binary case of the value representation proposition in Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), §5.10, printed pp. 95–96 (PDF pp. 101–102). The Lean proof derives it from the rank-three isotropy theorem of Springer's appendix, Theorem 5.3.3(i), printed pp. 109–110 (PDF pp. 115–116).
