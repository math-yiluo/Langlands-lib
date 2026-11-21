# Upper block matrices in the split tail

`packedTail` assembles the upper unipotent matrix with identity leading block, rectangular upper right block and upper unipotent trailing block. Multiplying two such matrices adds the second rectangle to the product of the first rectangle and the second tail. This gives the corrected first-column factorization used with `splitTailRectangle`. Conjugation by the embedded leading general linear matrix multiplies the rectangle on the left and fixes the tail block.

When the first column of the rectangle vanishes, the simple-root sum of the assembled matrix is the simple-root sum of the tail. The later physical columns and the preceding transposed columns give the exact column vectors used by the triangular Fourier identity. The proofs use consecutive matrix blocks and finite-index decomposition. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, Lemma 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
