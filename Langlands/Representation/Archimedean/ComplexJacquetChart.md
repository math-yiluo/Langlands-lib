# A chart of the matrices at the identity adapted to `B · U(n)`

Module: `Langlands.Representation.Archimedean.ComplexJacquetChart`.

## Purpose and provenance

This is the fourth helper module for `Langlands.Archimedean.complexJacquetFrobenius` (see
`ComplexJacquetFrobeniusProof.md`). To prove that the Frobenius function
`βκ ↦ χ(β) ℓ(ρ(κ) w)` is smooth near the identity, the factors `β` (upper triangular) and `κ`
(unitary) of `g = βκ` must depend smoothly on `g` near `1`, at least for some choice of the
factorization. This module provides such a choice through an explicit chart and the inverse
function theorem.

The underlying fact is that the Iwasawa decomposition `GL_n(ℂ) = B · U(n)` is a smooth
decomposition, and on the Lie algebra level `𝔤𝔩_n(ℂ) = 𝔟_ℝ ⊕ 𝔲(n)`, where `𝔟_ℝ` is the real
subspace of upper triangular matrices with real diagonal. The module makes no literature claim
beyond this. `skewPart`, `upperPart` and `chart` are auxiliary definitions of this formalization.

## Construction

Every complex `n × n` matrix `X` splits as `X = P_b X + P_u X` with

- `P_u X = L − Lᴴ + i Im diag(X)`, where `L` is the strictly lower triangular part of `X`; this is
  skew-Hermitian;
- `P_b X = X − P_u X`, which is upper triangular with diagonal `Re X_jj`.

Both maps are real-linear. The chart is `Φ(X) = (1 + P_b X) exp(P_u X)`. It is `C^∞` (over `ℝ`),
`Φ(0) = 1`, and its derivative at `0` is `X ↦ P_b X + P_u X = X`, the identity (product rule with
`D exp(0) = id`). The `C^∞` inverse function theorem (Mathlib's `ContDiffAt.localInverse`) then
gives a `C^∞` local inverse `Ψ` of `Φ` at `1`.

## Declarations

All declarations are in the namespace `Langlands.Archimedean`.

- `skewPart` (definition): the real-linear map `P_u`, with entries `X_ij` below the diagonal,
  `−conj(X_ji)` above it and `i Im X_jj` on it; `skewPart_apply` unfolds it.
- `star_skewPart`: `P_u X` is skew-Hermitian.
- `upperPart` (definition): the real-linear map `P_b = id − P_u`.
- `upperPart_add_skewPart`, `upperPart_apply`: `P_b X + P_u X = X` and the entries of `P_b X`.
- `upperPart_isUpperTriangular`, `upperPart_diag`: `P_b X` is upper triangular with diagonal
  entries `Re X_jj`.
- `one_add_upperPart_isUpperTriangular`: `1 + P_b X` is upper triangular.
- `chart` (definition): `Φ(X) = (1 + P_b X) exp(P_u X)`.
- `chart_zero`, `contDiff_chart`, `hasFDerivAt_chart`: `Φ(0) = 1`, `Φ` is `C^∞`, and its
  Fréchet derivative at `0` is the identity.
- `exists_chartInverse`: there is a map `Ψ` that is `C^∞` at `1`, with `Ψ(1) = 0`, `Ψ(y) → 0` as
  `y → 1`, and `Φ(Ψ(y)) = y` for all `y` in a neighbourhood of `1`.
- `eventually_diag_ne_zero`: for `X` near `0`, all diagonal entries of `1 + P_b X` are nonzero.

So near `1` every matrix `y` is `(1 + P_b Ψ(y)) · exp(P_u Ψ(y))`: an upper triangular matrix with
nonzero diagonal times a unitary matrix, and both factors are `C^∞` in `y`.
