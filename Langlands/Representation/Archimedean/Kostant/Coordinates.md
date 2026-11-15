# Coordinates on a finite product of matrix algebras

`Coord n = Σ i, Fin (n i) × Fin (n i)` indexes the matrix entries of `∏ᵢ 𝔤𝔩_{n i}`.
`blockMatrix n K i` is the generic matrix `(X ⟨i, p, q⟩)_{p,q}` of block `i` over the polynomial
ring `K[X_c]`, and `genericBlock n i` is the same matrix for `K = ℂ`
(`blockMatrix_complex` records that the two agree).
