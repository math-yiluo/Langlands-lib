# Image and diagonal normalization of Hermitian root matrices

This internal continuation of `HermitianRootMatrices` identifies its upper
matrix subgroup and realizes the parameter scaling by actual diagonal
conjugation. It does not assert generation or group-scheme classification.

An upper block-unipotent matrix has independent top-middle row `a`,
middle-bottom column `b` and top-bottom scalar `z`; its diagonal blocks are
`1,I,1` and its lower blocks vanish. `IsUpperBlockUnipotent` expresses exactly
this shape. The image of the parameter embedding is precisely the set of
general-linear matrices with this shape that preserve `gram H`.

For the reverse inclusion, the middle-bottom entries of the form-preservation
identity force `a i = w i * bar(b i)`. Its bottom-bottom entry gives
`z + bar(z) = Σ i, w i*bar(b i)*b i`. Thus the vector `bar(b)` and scalar `z`
are actual root parameters whose matrix is the given matrix. No weight is
inverted, so this characterization also permits degenerate middle forms.

For every unit `r`, `diagonalEmbedding r` is the general-linear matrix
`diag(r,I,r⁻¹)`. It is multiplicative in `r` and has determinant one. When
`bar(r)=r` it preserves the Hermitian form, and conjugating an upper root
matrix by it sends `(x,z)` to `(r*x,r²*z)`. This is exactly the existing
parameter endomorphism `scale r`. The conjugation identity is proved both for
matrices and for the general-linear embedding.

All claims follow by entrywise matrix algebra and finite-sum identities from
the preceding coordinate construction. Coefficient and index universes are
independent. The hypotheses are a commutative ring, its involution, a finite
index type with decidable equality, fixed diagonal weights, and, for the
form-preserving diagonal and scaling claims, the displayed fixed-unit
condition. There is no characteristic, field or nondegeneracy assumption.
