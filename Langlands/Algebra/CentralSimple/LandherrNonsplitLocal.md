# Local solutions of reduced norm one at a nonsplit completion

Module: `Langlands.Algebra.CentralSimple.LandherrNonsplitLocal`.

Setting as in `Langlands.Algebra.CentralSimple.LandherrNonsplit`: `d` is not a square in the
field `K`, `τ : FirstKindInvolution F B` acts on `E` by the conjugation (`hτ`), and `K` has
the unitary splitting property `UnitaryInvolutionSplitting K` (module
`Langlands.Algebra.UnitaryInvolutionStatements`).

- `relNorm F E B R z = reducedNorm E B (E ⊗_F R) (UnitaryPoints.tensorEquiv F E B R z)` is
  the relative reduced norm `R ⊗_F B → E ⊗_F R` for every commutative `F`-algebra `R`,
  defined on all elements (not only units). `nonsplitCenterEquiv_relNorm` identifies it at
  `K` with the reduced norm of `K(√d) ⊗_E B`.
- `nonsplitConjHom`, `nonsplitConjInvolution`: the conjugation of `K(√d)` as a ring
  endomorphism and as an algebra involution over `K`; `nonsplit_isQuadratic` and
  `nonsplit_isSeparable` make `K(√d)/K` a separable quadratic extension.
- `exists_nonsplit_chart`: there are an isomorphism `e : K(√d) ⊗_E B ≃ M_m(K(√d))` and an
  invertible Hermitian matrix `H` (`ct H = H`, with `ct` the conjugate transpose of
  `Langlands.Algebra.CentralSimple.LandherrHermitianUnitary`) such that
  `e (θ z) = H⁻¹ ct(e z) H`, where `θ = nonsplitInvolution F E B K τ`.
- `ct_mul_nonsplit`, `ct_one_nonsplit`, `det_ct_nonsplit`: `ct` reverses products, fixes
  `1` and conjugates determinants.
- `relNorm_baseChange_nonsplit`: `relNorm (τ_K z) = centerConj (relNorm z)`.
- `exists_commutator_solution`: if `y = x τ_K(x)` for units `x, y` of `K ⊗_F B` and
  `relNorm y = 1`, then `y = w τ_K(w)` for a unit `w` with `relNorm w = 1` lying in the
  commutator subgroup of `(K ⊗_F B)ˣ`.

## Proofs

`exists_nonsplit_chart`: `θ` is a unitary involution
(`nonsplitInvolution_isUnitary`), so the splitting property gives `K(√d) ⊗_E B ≅ M_m(K(√d))`
(with `m` the reduced degree, `matrix_size_eq_reducedDegree`). Transporting `θ` gives an
involution of the matrix algebra acting on scalars by the conjugation, which is the adjoint
involution of an invertible Hermitian Gram matrix by
`exists_hermitianGram_of_matrixInvolution` (module
`Langlands.Shimura.Unitary.HermitianAdjointChart`).

`relNorm_baseChange_nonsplit`: in the chart, the reduced norm is the determinant
(`reducedNorm_eq_chart_det`), and `det (H⁻¹ ct(X) H) = star (det X)`; transport back with
`nonsplitCenterEquiv_relNorm` and `nonsplitCenterEquiv_centerConj`.

`exists_commutator_solution`: let `X` be the matrix of `x`. From `y = x τ(x)` and
`relNorm y = 1`, `det X · star(det X) = 1`; put `δ = (det X)⁻¹`, so `c(δ) δ = 1`.
`H⁻¹` is Hermitian and nonzero, so `exists_unitary_det` gives `g` with
`g H⁻¹ ct(g) = H⁻¹` and `det g = δ`. Then `W = X g` satisfies
`W (H⁻¹ ct(W) H) = X (H⁻¹ ct(X) H)`, the matrix of `y`, and `det W = 1`. Thus `W` lies in
the commutator subgroup of `GL_m(K(√d))` by `mem_commutator_of_det_eq_one`
(module `Langlands.Algebra.CentralSimple.LandherrElementary`, using `2 ≠ 0`), and the unit
`w` of `K ⊗_F B` corresponding to `W` has all three properties.

## Provenance

At a place that does not split in `E`, the algebra with involution becomes a matrix algebra
with the adjoint involution of a Hermitian form, and a local solution of `y = x τ(x)` can be
corrected by a unitary matrix of prescribed determinant to have reduced norm one: Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), §5.5, Step 2 of the proof of
Lemma 1, printed p. 74 (PDF p. 80). The additional statement that the corrected solution
lies in the commutator subgroup is used to write it through elementary matrices
(module `Langlands.Algebra.CentralSimple.LandherrLocalTarget`).
