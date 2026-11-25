# Gauss integrals of Hermitian quadratic characters

**GKT Proposition 11.3** (p. 309) and **Corollary 11.4** (p. 315) in Case `3₊`, in the language of
Gauss integrals (the phase of a Gauss integral is the Weil index, Corollary 3.12, p. 80): the Weil
index of the quadratic form of `L ⊗ V` as a function of `det L`.

The module `Langlands.Theta.DualPair.TensorInvariants` computes the regularized integral of the
character of second degree `x ↦ ψ(½ β(x, x b))` on `M_{α×ν}(E)`. All its declarations are internal
(namespace `Langlands.Theta.Unitary.Internal`).

## Content

Let `β = hermitianPairing c Q` for an invertible Hermitian `Q` and `b ∈ M_ν(E)` Hermitian and
invertible.

- `hasGauss_herm`: there is `γ₀` with
  `HasGaussIntegral μ (x ↦ ψ(½ β(x, x b))) (γ₀ · splittingScalar F χ |α| (det b)⁻¹)` for every such `b`.
  Its argument is the Weil index of the quadratic form `f(x) = ½ β(x, x b)` (A. Weil, *Sur certains
  groupes d'opérateurs unitaires*, Acta Math. 111 (1964): `γ(f)`, of modulus one, is defined in
  chapter I, n° 14, Theorem 2, p. 161, and chapter II, n° 27, pp. 174–175, shows that the integral
  `g(f)` of `ψ ∘ f` over large lattices stabilizes, with `γ(f) = g(f)/|g(f)|`); the regularized
  integral here is `g(f)` itself. It is computed as follows.
- Write `Q = u D' c(u)ᵀ` and `b = a D c(a)ᵀ` with `D', D` diagonal with entries in `F`
  (`IsQuadraticInvolution.exists_eq_mul_diagonal_mul`). Then
  `½ β(x, x b) = ∑ ½ D'_i D_j N((uᵀ x a)_{ij})` (`pr_diag_norm`), a sum of scaled norm forms of
  the entries of `uᵀ x a`.
- `hasGauss_diag_norm`: the product over the entries of the Gauss integrals of the norm form
  (`hasGauss_norm_mul`, `HasGaussIntegral.pi`), transported to matrices.
- The change of variables `x ↦ uᵀ x a` scales Haar measure by `|N det u|^{|ν|} |N det a|^{|α|}`
  (`map_mul_mul_addHaar`), and the product of the `η(t) |t|⁻¹` is identified with the splitting
  scalar of `(det b)⁻¹` (`sc_det_inv`, using the multiplicativity of the quadratic character).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, files under
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/`:
`GaussIntegralDiagonalHermitianFormMatrices.lean`, `HermitianMatrixColumnPairingDiagonalNorm.lean`,
`HasGaussIntegralHermitianQuadraticCharacter.lean` (each whole). The repository has no licence
file; the text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.KSp`, `KSp.GaussMain` → `Langlands.Theta.Unitary.Internal`.
- Calls of the wrappers replaced by the wrapped lemmas: `exists_GL_diagonal_congruent_hermitian` →
  `IsQuadraticInvolution.exists_eq_mul_diagonal_mul`, `hasGaussIntegralCompactOpen_pi` →
  `HasGaussIntegral.pi`, `hasGaussIntegral_comp_addEquiv_rescale` →
  `HasGaussIntegral.comp_addEquiv`, `map_twoSided_mul_haar_matrix_quadraticExt` →
  `map_mul_mul_addHaar`, the others by the lemmas of the neighbouring files.
- `nabs` → `distribHaarChar` with explicit casts.

## Declarations

None public.

## Dependencies

`Langlands.Theta.WeilIndex.NormForm`, `Langlands.Theta.DualPair.LerayCharacter`.
