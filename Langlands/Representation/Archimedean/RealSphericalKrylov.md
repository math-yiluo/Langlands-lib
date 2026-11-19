# A cyclic vector for a lower triangular operator

Lean module: `Langlands.Representation.Archimedean.RealSphericalKrylov`, namespace
`Langlands.Archimedean.RealSphericalKrylov`. The module is linear algebra over `ℂ` and imports
only Mathlib. It is the finite-dimensional input of the proof of
`RealSphericalCyclicStatement` (module `RealSphericalCyclicProof`). There, `sOp` describes how
one step of right derivatives acts on the coefficients of quadratic functions on `O(n)`
(module `RealSphericalStep`).

## Definitions

- `sOp s` for `s : Fin N → ℂ` is the linear operator on `ℂ^N` given by
  `(S p)_l = s_l p_l − ∑_{i < l} p_i`. It is lower triangular with diagonal `s`
  (`sOp_apply`).
- `consZero k` is the linear embedding `w ↦ (0, w)` of `ℂ^k` into `ℂ^{k+1}` (`Fin.cons 0 w`).

## Lemmas

- `sOp_consZero`: `S(s) ∘ consZero = consZero ∘ S(s')` with `s' = Fin.tail s = (s_1, …, s_k)`.
  The first coordinate of `(0, w)` contributes nothing to the sums.
- `sOp_sub_one`: `(S(s) − s_0) 1 = (0, (S(s') − (s_0 + 1)) 1)`, where `1` is the all-ones
  vector. The coordinate `0` cancels, and for `l = j + 1` the sum over `i < l` has one extra
  term `p_0 = 1`, which shifts `s_0` to `s_0 + 1`.
- `aeval_comp_of_comp`: if `A ∘ ι = ι ∘ B`, then `P(A) ∘ ι = ι ∘ P(B)` for every polynomial
  `P`. The proof treats powers by induction and polynomials by `Polynomial.induction_on'`.
- `aeval_mem`: a subspace invariant under `A` is invariant under every `P(A)`.

## The main lemma `single_last_mem`

Let `s : Fin (k+1) → ℂ` with `s_k − s_j − 1 ≠ 0` for all `j < k`. Let `Z ⊆ ℂ^{k+1}` be an
`S(s)`-invariant subspace containing `P(S(s)) 1` for a polynomial `P` with `P(s_k) ≠ 0`. Then
`Z` contains the last standard basis vector `Pi.single (Fin.last k) 1`.

Proof by induction on `k`, peeling off the index `0`.

- `k = 0`. `S(s)` is the scalar `s_0`, so `P(S(s)) 1 = P(s_0) · 1`. Since `P(s_0) ≠ 0`, the
  vector `1`, which is the last basis vector of `ℂ^1`, lies in `Z`.
- `k + 1`. Put `s' = Fin.tail s`, `Z' = consZero⁻¹(Z)`, and `P' = P · (X − (s_0 + 1))`.
  Then:
  1. `Z'` is `S(s')`-invariant, by `sOp_consZero`.
  2. `P'(s'_{last}) = P(s_{last}) · (s_{last} − s_0 − 1) ≠ 0`, using the hypothesis for
     `j = 0`.
  3. The hypothesis on `s'` follows from the one on `s` for the indices `j + 1`.
  4. `(S(s) − s_0) P(S(s)) 1 = P(S(s)) (S(s) − s_0) 1 = consZero (P'(S(s')) 1)`. This uses
     `sOp_sub_one` and `aeval_comp_of_comp`. The left side lies in `Z` by `aeval_mem`, so
     `P'(S(s')) 1 ∈ Z'`.
  5. By induction the last basis vector of `ℂ^{k+1}` lies in `Z'`. Its image under
     `consZero` is the last basis vector of `ℂ^{k+2}`.

## Provenance

The lemma and its proof were written for this project. In the cyclicity proof, `S` is the matrix
of the step formula of `RealSphericalStep`, with `s_l = α_l + l`. The hypothesis
`s_k − s_j − 1 ≠ 0` is where the closed Langlands chamber enters.
