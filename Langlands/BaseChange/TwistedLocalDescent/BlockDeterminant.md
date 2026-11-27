# The determinant of the adjoint action on the strictly block lower matrices

Module `Langlands.BaseChange.TwistedLocalDescent.BlockDeterminant`. For `m` in the standard
block Levi `M(E)` of a block shape `B`, the map `X ↦ m X m⁻¹` preserves the strictly block lower
matrices `𝔲̄(E)` (`lowerAdjoint B m`, an `E`-linear endomorphism).

`det_lowerAdjoint`: its determinant is
`∏_{k < i} det(m_i)^{n_k} · det(m_k⁻¹)^{n_i}`, the product over pairs of blocks `(i, k)` with
`k < i` (row block `i`, column block `k`), `n_i` the size of block `i`.

Proof: the matrix units `E_ab` with `a` in block `i`, `b` in block `k`, `k < i`, form a basis
(`lowerBasis`) indexed by `LowerPosition`. Grouping it by the block pair `(i, k)` (`pairCode`),
the matrix of `lowerAdjoint` is block triangular (`blockTriangular_toMatrix_lowerAdjoint`:
`m E_ab m⁻¹` only involves positions of the same block pair, since `m` is block diagonal), so the
determinant is the product of the diagonal blocks. The diagonal block of the pair `(i, k)` is the
Kronecker product `m_i ⊗ (m_k⁻¹)^T` (`toMatrix_lowerAdjoint_apply`, `lowerBlockEquiv`), whose
determinant is `det(m_i)^{n_k} det(m_k⁻¹)^{n_i}` (`det_toSquareBlock_lowerAdjoint`,
`Matrix.det_kronecker`).
