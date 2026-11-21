# Smooth Iwasawa factors in mixed archimedean coordinates

`matrixPlaceCoordinates` identifies the actual mixed archimedean matrix algebra with the product of its real and complex matrix spaces by a continuous real linear equivalence. The inverse assembles entries from their place coordinates. `mem_standardInfiniteCompact_iff_mem_unitary` identifies the actual standard infinite compact with the unitary group of the mixed matrix algebra.

`exists_smoothLocalIwasawa_at_one` combines the published real and complex local Iwasawa charts. Each chart gives an upper triangular factor and the exponential of a skew-adjoint matrix. Both assembled factors equal the identity and satisfy `ContDiffAt ℝ ∞` at the mixed identity. The differentiability neighborhood can depend on the finite order. There are finitely many archimedean places, so the factorization identity, upper triangularity, and unitarity hold together on a neighborhood of the identity. On a neighborhood where the matrix being factored is invertible, the upper factor is invertible as well.

`exists_smoothLocalIwasawa` gives factors with `ContDiffAt ℝ ∞` at an arbitrary invertible archimedean matrix and the same factor identities on a neighborhood of that matrix. The proof chooses ordinary Iwasawa factors and multiplies by their inverses on the left and right to reduce to the identity chart. Multiplying by the original factors restores the decomposition near the chosen matrix.

The smooth chart is an internal consequence of the published real and complex local inverses and the actual mixed matrix coordinates. Getz and Hahn (2024), §10.1, p. 270 (PDF 282), use the standard compact and Iwasawa decomposition in adelic induction.
