# The rational Cartan square sum on actual real general linear groups

This internal module specializes the rational mixed coordinates of [RealMixedMatrixCoordinates](RealMixedMatrixCoordinates.md) to the actual group `GL_n(ℝ)`. It identifies the compact group and the Cartan square sum used by [MixedOrbitCoefficient](MixedOrbitCoefficient.md).

- `Langlands.Archimedean.cartanPositiveForm_star_conj`: for any number field `K` and a mixed matrix `u` with `u u* = 1`, the published `cartanPositiveForm` is invariant under `X ↦ u* X u`. Its value is the total mixed trace of `tr(X Y*)`. The conjugated product is `u*(X Y*)u` because `u u* = 1`, and the trace is cyclic.

In `Langlands.Archimedean.RealCartan`, with `ψ = rationalMixedMatrixEquiv n`:

- `realCartanEquiv` is the real linear equivalence of the rational real matrix Lie algebra with actual real matrices, through `ψ`. `realCartanForm` is the positive Cartan form transported to real matrices. `realCartanBasis` is the transported normalized basis `cartanAdaptedBasis ℚ n`.
- `realCartanForm_symm` and `realCartanBasis_pair`: the form is symmetric, and the basis is orthonormal (`cartanPositiveForm_symm`, `cartanAdaptedBasis_pair`).
- `realCartanForm_conj`: for `k` in the actual orthogonal subgroup `unitaryCompact ℝ n`, the transported form is invariant under `X ↦ k⁻¹ X k`. Since `k⁻¹ = kᵀ`, pulling back by `ψ` gives conjugation by `u = ψ⁻¹(k)`, with `u⁻¹ = u*` and `u u* = 1` by `rationalMixedMatrixEquiv_star`.
- `transportedCartanSquareSum_eq`: the transported Cartan square sum of a representation `R` of `GL_n(ℝ)` is the orthonormal square sum `basisSquareSum R realCartanBasis` of [SmoothOrthonormalSquareSum](SmoothOrthonormalSquareSum.md).
- `transportedCartanSquareSum_representation`: this operator commutes with `R∞(k)` for every orthogonal `k`, by `basisSquareSum_representation`.
- `exists_unitaryCompact_mem_connectedComponent`: every point of the rational completion-based group lies in the connected component of a point whose image in `GL_n(ℝ)` is orthogonal. The composite of the published coordinates with the units equivalence is a homeomorphism. The published `exists_unitary_mem_connectedComponent` puts every real invertible matrix in the component of an orthogonal one, and the inverse map carries this connected component into the component in the completion-based group.
