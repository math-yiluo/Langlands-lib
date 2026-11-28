# Local reduced norms from approximate norm-one corrections

Module: `Langlands.Algebra.CentralSimple.LandherrEichlerLocal`.

Setting: `E/F` separable quadratic with `CharZero F`, `r = skewRoot F E`, `B` a
finite-dimensional central simple `E`-algebra, `relNorm` the relative reduced norm and
`qm p q = 1 ⊗ p + r ⊗ q` (module `Langlands.Algebra.CentralSimple.LandherrTensorQuadratic`).

- `conjugation_add_mul_skewRoot`: `σ(p + q r) = p - q r` for `p, q ∈ F`.
- `exists_reducedNorm_near_hilbert90`: let `K_v` be a topological field over `F`, `E_w` a
  complete nontrivially normed field of characteristic zero over `E`, and `φ : K_v → E_w` a
  continuous ring map compatible with `F → E → E_w`. Let `x` be a unit of `K_v ⊗_F B`,
  `t₀ ∈ E`, and `ω_v = qm P₀ Q₀` a unit with `relNorm x · σ(ω_v) = (t₀ ⊗ 1) ω_v`. Then there
  is a neighbourhood `U` of `(P₀, Q₀)` such that for all `p, q ∈ F` whose images lie in `U`,
  `ω = p + q r ≠ 0` and `t₀ ω / σ(ω)` is the reduced norm of a unit of `E_w ⊗_E B`.

## Proof

The `E`-algebra map `ψ : E ⊗_F K_v → E_w`, `e ⊗ k ↦ e φ(k)`, sends `ω_v` and `σ(ω_v)` to
`N₀ = φ P₀ + r φ Q₀ ≠ 0` and `D₀ = φ P₀ - r φ Q₀ ≠ 0`, and the hypothesis becomes
`t₀ = δ_w D₀ / N₀` with `δ_w = ψ(relNorm x)` the reduced norm of the image `x_w` of `x` in
`E_w ⊗_E B`. With `κ = D₀ / N₀`, the quotient `κ (φ P + r φ Q) / (φ P - r φ Q)` equals `1` at
`(P₀, Q₀)`, so by `ratio_preimage_mem_nhds` and `powSet_mem_nhds` (module
`Langlands.Algebra.CentralSimple.LandherrPowNeighborhood`) it is an `n`-th power `sⁿ`,
`s ≠ 0`, of an element of `E_w` for `(P, Q)` near `(P₀, Q₀)`, where `n` is the reduced degree
of `B`. For such `p, q`, `t₀ ω / σ(ω) = δ_w · sⁿ`, which is the reduced norm of
`x_w · (s ⊗ 1)`.

## Provenance

This is the local step of the reduction of Landherr's theorem to elements of reduced norm one
in Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.5, printed p. 77
(PDF p. 83): if the global norm `z·u` is close to the local reduced norm `N x_v`, their
quotient is an `n`-th power and hence `z·u` is a local reduced norm.
