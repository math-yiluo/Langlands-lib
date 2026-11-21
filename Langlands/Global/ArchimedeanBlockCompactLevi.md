# Compact Levi coordinates over the real and complex fields

`compactLeviEmbedding` sends an ordered tuple of compact block matrices to the compact subgroup of the ambient general linear group. The inverse of the block diagonal matrix has the same diagonal blocks as the conjugate transpose. Equality of those matrices verifies the compact condition.

`compactLeviProjection` extracts the compact diagonal blocks of a compact parabolic element. The inverse is also parabolic and its matrix is the conjugate transpose of the original matrix. The lower block zeros of the inverse therefore give upper block zeros of the original matrix. The original lower block zeros and the formula for its diagonal blocks prove that the compact parabolic element equals the block diagonal embedding of this projection.

This is an internal matrix comparison for normalized compact induction. It applies to the actual ordered `BlockShape` over both ℝ and ℂ. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), use the standard compact subgroup and parabolic in the scalar compact model.
