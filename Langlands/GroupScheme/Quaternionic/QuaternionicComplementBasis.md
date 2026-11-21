# Quaternion bases from a complementary subspace

Let `Q` be quaternion coordinates for a division algebra `D` over `F`, with the embedded quadratic field `E`. Regard a left `D`-space as an `E`-space using the embedding. If an `E`-subspace `W` and its semilinear image under the second quaternion generator are complementary, the vectors of any finite `E`-basis of `W` form a `D`-basis of the entire space.

To verify this, decompose every quaternion coefficient as `ι(a) + j ι(b)`. The quaternion linear combination is the sum of the two `E`-linear combinations, with the second translated by `j`. The direct-sum condition gives injectivity, and the basis coordinates on both components give surjectivity. The resulting quaternion-linear equivalence takes the standard basis to the given vectors.

This coordinate fact is derived from the complementary-subspace construction in Springer's appendix to Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i), printed p. 110 (PDF p. 116). It permits extending the induced Hermitian coordinates alongside the original skew form.
