# Volumes and transversality for Levi descent

`descentProjection` projects the fine normal space of a Levi flat onto the noncentral part of the coarse flat. Its norm determinant agrees with the descent coefficient when the coarse and normal dimensions match. Indeed, the concatenated Gram matrix of the prescribed orthonormal bases has an identity block for the complement of the coarse space. The Schur complement removes the components in that complement. On the noncentral part of the fine space, this removal gives the coarse orthogonal projection.

A nonzero coefficient therefore characterizes bijectivity of `descentProjection`. The norm determinant composes with a change of basis in the normal space. This identifies the descent coefficient times the volume of that basis with the volume of its projected vectors.

For a bijective projection, the affine intersection is found by transporting the functional `w ↦ -⟪w, ξ⟫` to the coarse space and representing it by inner product. This gives the unique coarse displacement that makes the resulting vector orthogonal to the Levi normal space. `descentSection_eq_posSet` identifies the chosen section with its signs.

`gramVolume_join_orthogonalProjection` computes the Gram volume of an orthonormal basis of a subspace `U` joined to a family `w`: it is the Gram volume of the components of `w` orthogonal to `U`. In particular it does not depend on the orthonormal basis of `U`.

The volume and section are those of Arthur, *An introduction to the trace formula*, §17, printed pp. 99–100. The retained source is `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
