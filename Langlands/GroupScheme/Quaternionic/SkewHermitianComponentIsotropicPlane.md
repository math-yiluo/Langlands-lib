# Isotropic planes in the symmetric component

Use quaternion coordinates `Q` for a skew-hermitian pairing `B` over `F`,
with embedded quadratic field `E`. Let `R` be a field extending `E`. Assume that
vectors `t,s` in the scalar extension over `F` satisfy `B_R(t,t) = 0` and
`B_R(t,s) = 1`. `SymmetricComponentIsotropicPairStatement` gives two independent
orthogonal isotropic vectors for the extension over `E` of the symmetric component.

Project `t` and `j t` from `R ⊗[F] V` to `R ⊗[E] V`. All their pairings in the
symmetric component vanish because their original skew pairings vanish. To prove
independence, pair a potential linear relation against `s`. The first quaternion
coordinate vanishes on the kernel of the tensor projection and takes the values
`1,0` on `t,j t`. Pairing their projections against the projection of `s` in the
symmetric component gives the values `0,1`. Both coefficients of the relation are
therefore zero.

This is the isotropic-plane calculation for Springer, appendix to M. Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i),
printed p. 109 (PDF p. 115).
