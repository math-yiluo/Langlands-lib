# Real triangular entry changes of variables

For a full diagonal `d : Fin n → ℝˣ`, the upper entries of `diag(d) u(X)` are `(dᵢ Xᵢⱼ)ᵢ<ⱼ`, and those of `u(X) diag(d)` are `(dⱼ Xᵢⱼ)ᵢ<ⱼ`; both matrices have diagonal `d` and zero lower entries. Here `u(X)` is the inverse of `upperEntryCoordinates`.

`map_scale_realUpperEntries` gives the product Haar pushforward for an independent nonzero real scale on each strictly upper entry. Its factor is the product of the reciprocal absolute values of these scales.

`integral_realDiagonal_mul_upperEntries` and `integral_realUpperEntries_mul_diagonal` implement these changes of variables for continuous Banach-valued integrands (Lean's Bochner integral, including the default value outside integrability) and a product of the supplied additive Haar measure on `ℝ`. Their factors are respectively `∏_{i<j} |dᵢ|⁻¹` and `∏_{i<j} |dⱼ|⁻¹`. The proofs apply the one-dimensional Haar scaling formula and the diagonal product-measure map theorem; the row and column counts are given by the finite upper and lower intervals in `Fin n`.

This is an internal measure calculation for the matrix-integral argument in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §4.7, pp. 30–31. It supplies real analogues of the Library's complex triangular changes of variables. It does not identify the resulting representation weights or prove convergence of a global matrix integral.
