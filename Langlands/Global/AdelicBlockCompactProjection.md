# Levi projection on the adelic compact intersection

Let \(P\) be the standard upper block parabolic and \(K\) the standard compact subgroup of the actual adelic general linear group. `compactIntersection` is the subgroup of parabolic elements whose matrices lie in \(K\). `compactLeviProjection` is the continuous homomorphism from this subgroup to the product of the standard compact subgroups of the diagonal blocks. Its value in each block is the actual diagonal-block projection.

At a finite place, the block entries are entries of the original integral matrix. The block inverse is the diagonal block of the parabolic inverse because Levi projection is a homomorphism. Thus the entries are integral in both directions. At a real or complex place, a compact matrix has inverse equal to its conjugate transpose. Extracting the same diagonal block on both sides identifies the inverse of the block with its own conjugate transpose. This proves the orthogonal or unitary condition for that local block. The published finite and infinite projection formulas assemble these two conclusions on the actual adelic Levi.

The determinant norm of each projected block is one. The proof uses the published fact that a continuous positive character is trivial on a compact subgroup. The pairwise formula for the Levi character then gives one, and the constructed positive half character is also one. This removes the scalar twist from covariance when the parabolic element lies in \(P\cap K\).

These internal group and character identities use the actual matrix groups and their standard compact subgroups. The related compact normalization in Getz and Hahn (2024), §10.1, p. 270 (PDF 282), is the vanishing of \(H_M\) on \(K\cap M(\mathbb A_F)\) in the notation of (10.1).
