# One Lie step on quadratic functions of the compact group

Lean module: `Langlands.Representation.Archimedean.RealSphericalStep`, namespace
`Langlands.Archimedean.RealSphericalStep`. It imports `RealBlockLeftDerivative` and
`RealSphericalKrylov`, and it is part of the proof of `RealSphericalCyclicStatement`.

Notation: `N ∈ ℕ`. `φ` is a smooth function on `GL_N(ℝ)` (`ContMDiff` for `matrixModel ℝ N`)
that is exponent-equivariant for `α : Fin N → ℂ` in the sense of the Library's
`IsExpEquivariant α φ`: `φ(exp(diag x) u g) = exp(∑ α_i x_i) φ(g)` for `u` upper unipotent.
`R(X)` is the right derivative `rightDerivative (matrixModel ℝ N) X`. `E_{ac}` is
`Matrix.single a c 1`. `W_{ab} = rotGen a b = E_{ba} − E_{ab}`, and
`conjT X k = k X kᵀ`; both come from `RealPrincipalSeriesDuality`.

## Decomposition of a right derivative on `O(N)` (`rightDerivative_eq_decomp`)

For `k ∈ O(N)` and a matrix `X`, put `S = k X kᵀ`. Then

`R(X) φ (k) = (∑_i α_i S_{ii}) φ(k) + ∑_{a < b} S_{ba} · dφ̃_k(W_{ab} k)`,

where `φ̃ = unitsExtension φ` is the extension by zero to all matrices.

Proof. By the Library's `rightDerivative_eq_fderiv`, `R(X)φ(k) = dφ̃_k(k X)`. Write
`k X = (S − R) k + R k` with `R = ∑_{a<b} S_{ba} W_{ab}`; this uses `k kᵀ = 1`. The matrix
`S − R` is upper triangular with diagonal `S_{ii}` (`isUpperTriangular_sub_rotSum`,
`sub_rotSum_apply_self`). So the Library's `fderiv_upperTriangular_of_isExpEquivariant` gives
`dφ̃_k((S − R) k) = (∑ α_i S_{ii}) φ(k)`. The rest follows by linearity of `dφ̃_k`.

## Rotation derivatives (`fderiv_rot_eq`)

Let `φ = g ∘ (matrix)` on `O(N)` for some function `g` on matrices. Let `W` be skew-symmetric,
and suppose `t ↦ g(exp(tW) k)` has derivative `g'` at `0`. Then `dφ̃_k(W k) = g'`. The curve
`t ↦ exp(tW) k` stays in `O(N)` (`expK`), so `φ̃` and `g` agree along it. The chain rule then
identifies both derivatives.

## Quadratic functions

- `quad p c b M = ∑_l p_l M_{lc} M_{lb}`.
- `hasDerivAt_quad`: the derivative of `t ↦ quad p c b (exp(tW) M)` at `0` is
  `∑_l p_l ((WM)_{lc} M_{lb} + M_{lc} (WM)_{lb})`.
- `quad_rot`: for `W = W_{ij}` with `i ≠ j`, this derivative equals
  `(p_j − p_i)(M_{ic} M_{jb} + M_{jc} M_{ib})`. Only the rows `i` and `j` of `W_{ij} M` are
  nonzero (`single_mul_apply_eq`).

## The algebraic identity (`step_algebra`)

For `k ∈ O(N)`, `α, p : Fin N → ℂ` and indices `a, b`, the sum over `c` of

`(∑_i α_i k_{ia} k_{ic}) (∑_l p_l k_{lc} k_{lb})
  + ∑_{i<j} k_{ja} k_{ic} (p_j − p_i)(k_{ic} k_{jb} + k_{jc} k_{ib})`

equals `∑_l (S p)_l k_{la} k_{lb}`, where `S = sOp s` with `s_l = α_l + l`. The proof uses the
orthonormality of the rows of `k` (`sum_mul_eq_of_mem`):

- the first part sums to `∑_i α_i p_i k_{ia} k_{ib}`;
- the second part sums to `∑_{i<j} k_{ja}(p_j − p_i) k_{jb}`. This equals
  `∑_l (l p_l − ∑_{i<l} p_i) k_{la} k_{lb}` (`sum_lt_const` counts the `i < l`).

## The step formula (`sum_rightDerivative_single`)

Let `G_0, …, G_{N−1}` be smooth, all exponent-equivariant for the same `α`, with
`G_c(κ) = quad p c b κ` for `κ ∈ O(N)` and a fixed `b`. Then for every `a` and every `k ∈ O(N)`,

`∑_c R(E_{ac}) G_c (k) = ∑_l (S p)_l k_{la} k_{lb}`, where `S = sOp (α_l + l)`.

Proof. Apply `rightDerivative_eq_decomp` to each `G_c` with `X = E_{ac}`. The entries of
`k E_{ac} kᵀ` are `k_{xa} k_{yc}` (`conjT_single_apply`). The rotation derivatives are computed
by `fderiv_rot_eq`, `hasDerivAt_quad` and `quad_rot`. The resulting expression is exactly the
left side of `step_algebra`.

## Provenance

The module was written for this project. The step formula is the infinitesimal form of the
computation of `U(𝔤)` acting on `K`-types of the unramified principal series of `GL_N(ℝ)`.
Here it is used only for the quadratic functions `κ ↦ ∑_l p_l κ_{lc} κ_{lb}`. Its role in
the proof is to show that the regularized vector of `RealSphericalReach` lies in the
Lie-span of the spherical vector.
