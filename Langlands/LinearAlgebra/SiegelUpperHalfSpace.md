# The Siegel upper half space

The module `Langlands.LinearAlgebra.SiegelUpperHalfSpace` defines the Siegel upper half space and
proves the facts on it that the Gaussian vectors of the Weil representation need.

## Content

`Langlands.Matrix.IsSiegel Ω`: the complex square matrix `Ω` is symmetric and `Im Ω` is positive
definite; `Matrix.siegelUpperHalfSpace ι` is the set of such matrices. Elementary closure properties:
`X + iY` for `X` real symmetric and `Y` positive definite, diagonal matrices with entries in the
upper half plane (in particular `i · 1`), block diagonal matrices, principal submatrices, positive
multiples, real symmetric translates and real congruences `Pᵀ Ω P` stay in it. Every Siegel matrix
is `Pᵀ (diagonal t) P` with `P` real invertible and `Im tᵢ > 0`
(`Matrix.IsSiegel.exists_eq_transpose_mul_diagonal_mul`, a simultaneous diagonalization of the real and
imaginary parts); hence Siegel matrices are invertible and
`Ω ↦ -Ω⁻¹` preserves the space.

For `s = [[A, B], [C, D]]` real symplectic, `P = A - iB` is invertible and `-(Q P⁻¹)`, `Q = C - iD`, is
symmetric (`Matrix.det_ne_zero_and_isSymm_of_mem_symplecticGroup`, from the identities
`Pᴴ Q - Qᴴ P = -2i` and `Pᵀ Q = Qᵀ P` given by the symplectic relations) and Siegel
(`Matrix.IsSiegel.neg_mul_inv_of_symplectic`): it is the image of `i · 1` under `s` for the action of
`Sp_{2n}(ℝ)` by fractional linear transformations. These two statements keep the source's form, with `P` and `Q`
given by hypotheses on their entries; `Langlands.Theta.Real.Metaplectic.Gaussian` states them for
`automorphyUpper`, `automorphyLower` and `siegelPoint`.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean`, lines 13–125
(`IsSiegel` and its lemmas, without the four that mention `ReciprocityTheory.PTheta.SiegelH`);
`src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean`, lines 14–115;
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticHolPartDetNeZeroAndIsSymm.lean` and `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSiegelUpperHalfSpaceNegMulInvSymplectic.lean`
(whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- `GlobalTheory.IsSiegel` → `Langlands.Matrix.IsSiegel`; the lemmas move from `GlobalTheory` to
  `Langlands.Matrix` (`GlobalTheory.ofReal_mulVec_eq` → `Langlands.Matrix.ofReal_mulVec_eq`, …).
- The second definition of the space in the source (`ReciprocityTheory.PTheta.SiegelH`) and the lemmas
  comparing the two are not taken; the rest of the source files (Riemann theta functions, Poisson
  summation, lattices) is not taken.
- `SympBlocks.det_ne_zero_and_isSymm` → `Matrix.det_ne_zero_and_isSymm_of_mem_symplecticGroup`; its two
  auxiliary identities are private. The wrappers `GlobalTheory.T.*` of these files are not taken.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- def `Langlands.Matrix.IsSiegel`
- theorem `Langlands.Matrix.IsSiegel.mk`
- theorem `Langlands.Matrix.IsSiegel.isSymm`
- theorem `Langlands.Matrix.IsSiegel.posDef`
- def `Langlands.Matrix.siegelUpperHalfSpace`
- theorem `Langlands.Matrix.mem_siegelUpperHalfSpace`
- theorem `Langlands.Matrix.isHermitian_map_im_of_isSymm`
- theorem `Langlands.Matrix.IsSiegel.of_dotProduct_pos`
- theorem `Langlands.Matrix.IsSiegel.dotProduct_pos`
- theorem `Langlands.Matrix.isSiegel_ofReal_add_I_smul`
- theorem `Langlands.Matrix.isSiegel_diagonal_iff`
- theorem `Langlands.Matrix.isSiegel_I_smul_one`
- theorem `Langlands.Matrix.isSiegel_unique_iff`
- theorem `Langlands.Matrix.IsSiegel.smul`
- theorem `Langlands.Matrix.IsSiegel.natCast_smul`
- theorem `Langlands.Matrix.IsSiegel.submatrix`
- theorem `Langlands.Matrix.isSiegel_fromBlocks_iff`
- theorem `Langlands.Matrix.IsSiegel.exists_eq_transpose_mul_diagonal_mul`
- theorem `Langlands.Matrix.ofReal_mulVec_eq`
- theorem `Langlands.Matrix.isUnit_det_map_ofReal`
- theorem `Langlands.Matrix.inv_map_ofReal`
- theorem `Langlands.Matrix.IsSiegel.transpose_mul_mul`
- theorem `Langlands.Matrix.IsSiegel.isUnit_det`
- theorem `Langlands.Matrix.inv_diagonal_of_ne_zero`
- theorem `Langlands.Matrix.IsSiegel.neg_inv`
- theorem `Langlands.Matrix.IsSiegel.add_map_ofReal`
- theorem `Langlands.Matrix.det_ne_zero_and_isSymm_of_mem_symplecticGroup`
- theorem `Langlands.Matrix.IsSiegel.neg_mul_inv_of_symplectic`

## Dependencies

Mathlib only: `Analysis.Complex.Polynomial.Basic`, `Analysis.Matrix.Order`,
`LinearAlgebra.Matrix.PosDef`, `LinearAlgebra.Matrix.ToLinearEquiv`, `LinearAlgebra.SymplecticGroup`.
