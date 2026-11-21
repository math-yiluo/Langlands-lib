# The adelic unipotent complement of a single block cut

The matrix comparison for a single internal cut identifies the complement
of the coarse radical in the refined radical with the embedded two-block
radical of the specified block. `singleCutLeviMatrixEquiv` is the group
isomorphism given by that embedding. The inverse reads the specified
coordinate of the block diagonal matrix, which proves continuity in
the matrix model.

`singleCutLeviAdelicEquiv` transports the matrix isomorphism through the
existing affine-point comparisons. Evaluating it on the ambient adelic
points recovers the same single block embedding. The matrix embedding
commutes with the coefficient map, so the adelic isomorphism matches the
two principal rational lattices exactly.

This is the quotient group identification used for the Levi integrals in
Langlands (1979), Lemma 4 and the proof of Proposition 2, printed pp.
204–205 (Corvallis Part I, PDF pp. 199–200). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
