# Bounded matrix entries of central norm-kernel points

Author: Worker 1532.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Internal helper for the
proof of `CentralNormKernelCompactnessStatement`.

- `spectralNorm_sum_le`: the spectral norm on an algebraic extension of an ultrametric
  nontrivially normed field is subadditive on finite sums (from
  `isNonarchimedean_spectralNorm`).
- `exists_entry_bound`: let `F` be a nonarchimedean local field (norm
  `LocalGalois.localNormedField F`), `M` a group scheme over `Spec F` with `M.X.hom` affine and
  locally of finite type, `hU : HasTrivialUnipotentRadical (closureGroup M)`, and
  `ρ : MatrixRepresentation M N` a closed immersion. Then there is `C` with
  `‖ρ(z)_{kl}‖ ≤ C` for every `z` in `schemeCenterPoints M ⊓ rationalCommonNormKernel M` and all
  `k, l`.

Proof. Work over `K = AlgebraicClosure F` with `closureGroup M` (affine, locally of finite type)
and the closed immersion `closureRep ρ` (module `BaseChange`). Take a centre representative
over `K` (`schemeTheoreticCenterExistence_of_isAffineHom`); `finite_centralUnipotent` gives a
finite set `U` of central rational points with unipotent matrices; choose spectral data `D` for
the central algebra of `closureRep ρ`. Let `f u k l i` be the spectral norm of the
`(k, l)` entry of `E i ρ_K(u)` and `C = ∑_{u ∈ U} ∑_k ∑_l ∑_i f u k l i`.

For `z` in the intersection, `closurePoint z` is central, and
`exists_central_unipotent_decomposition` gives a central `u` with unipotent matrix (so `u ∈ U`)
and `ρ_K(z_K) = s ρ_K(u)`. By `closureRep_rationalMatrix` and `semisimpleMatrix_mul_apply`, the
image of `ρ(z)_{kl}` in `K` is `∑_i λ_i (E i ρ_K(u))_{kl}`. Each `λ_i` is a root of the
characteristic polynomial of `ρ_K(z_K)`, which is that of `ρ(z)` mapped to `K`
(`isRoot_charpoly_χ`, `Matrix.charpoly_map`), so `spectralNorm λ_i = 1`
(`spectralNorm_eq_one_of_mem_normKernel`). Hence, by `spectralNorm_extends`,
`spectralNorm_sum_le` and `spectralNorm_mul`, `‖ρ(z)_{kl}‖ ≤ ∑_i f u k l i ≤ C`.

The declaration carries `set_option maxHeartbeats 800000`.
