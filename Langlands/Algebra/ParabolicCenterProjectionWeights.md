# Weight bases for an abelian subspace and a regular grading element

Module `Langlands.Algebra.ParabolicCenterProjectionWeights`, namespace
`Langlands.Algebra.ParabolicCenterProjection`.

Let `g` be a complex Lie algebra, `𝔥` a subspace, `b : Basis I ℂ g` and `wt i : 𝔥 →ₗ[ℂ] ℂ`
with `⁅h, b i⁆ = wt i h • b i` for `h ∈ 𝔥` (hypothesis `heig`).

## Weight vectors and invariant forms

- `wt_eq_of_repr_ne_zero`: a common eigenvector `x` of `ad 𝔥` with eigenvalues `μ` has nonzero
  coordinates only on basis vectors of weight `μ` (via
  `LieWeightProjection.mem_eigenSpan_of_ad`).
- `lie_basis_eig`: `⁅b e, b i⁆` has weight `wt e + wt i`.
- `form_lie_add_form_lie`: an invariant form `B` satisfies `B ⁅h, x⁆ y + B x ⁅h, y⁆ = 0`.
- `wt_eq_neg_of_form_ne_zero`: `B (b e) (b i) ≠ 0` implies `wt e = -wt i`.

## A regular grading element

- `exists_re_ne_zero` (`I` finite): some `h' ∈ 𝔥` has `Re (wt i h') ≠ 0` for every nonzero
  weight. The kernels of the nonzero real-linear forms `Re ∘ wt i` are proper real subspaces,
  and a finite union of proper subspaces over the infinite field `ℝ` is not the whole space
  (Mathlib's `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`).
- `exists_int_wt`: if `H ∈ 𝔥` and the eigenvectors of `ad H` with integer eigenvalues span `g`,
  then every `wt i H` is an integer: `b i` is an eigenvector of `ad H`, and an eigenvector lies
  in the span of the eigenbasis vectors with the same eigenvalue.
- `exists_regular`: under the same hypotheses, some `H'' ∈ 𝔥` has `Re (wt i H'') = 0` exactly
  when `wt i = 0`, and `Re (wt i H'') > 0` whenever `wt i H` is a positive integer. Take
  `H'' = N H + h'` with `h'` from `exists_re_ne_zero` and `N` larger than every
  `|Re (wt i h')|`: integrality makes `N wt i H` dominate when `wt i H ≠ 0`.

## Provenance

Internal. The real parts of the weights at `H''` order the weights compatibly with the grading
by `H`, replacing the choice of a positive system that the classical theory makes with the
rationality of roots.
