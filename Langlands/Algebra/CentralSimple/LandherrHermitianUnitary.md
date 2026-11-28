# Unitary matrices of prescribed determinant for a Hermitian form

Module: `Langlands.Algebra.CentralSimple.LandherrHermitianUnitary`.

Let `L` be a field with a ring endomorphism `c` and let `n` be a finite index type.

- The map `ct c M = (M.map c)ᵀ` applies `c` entrywise and transposes the result.
  The lemma `ct_apply` gives its entries.
- The lemma `exists_anisotropic` gives a vector `u` with `c(u)ᵀ K u ≠ 0` when `K ≠ 0`
  and `c(b) ≠ b` for some `b ∈ L`.
- If also `c(c(x)) = x` for every `x`, `exists_unitary_det` applies to a nonzero
  Hermitian matrix `K` with `ct c K = K` and to `δ ∈ L` with `c(δ) δ = 1`. It gives
  a matrix `g` with `g K ct c g = K` and `det g = δ`.

## Proofs

`exists_anisotropic`: if `c(u)ᵀ K u = 0` for all `u`, then testing the basis vectors gives
`Kᵢᵢ = 0`; testing `eᵢ + t eⱼ` gives `t Kᵢⱼ + c(t) Kⱼᵢ = 0` for all `t`, and comparing
`t = 1` with `t = b`, where `c(b) ≠ b`, gives `(b - c(b)) Kᵢⱼ = 0`, so `K = 0`.

`exists_unitary_det`: choose an anisotropic `u` and put `w = K u`, `a = c(u)ᵀ K u`, which is
nonzero and fixed by `c` because `K` is Hermitian, and `s = (δ - 1) a⁻¹`. The matrix
`g = 1 + s w c(u)ᵀ` (a rank-one modification, a "quasi-reflection" along `w`) satisfies
`g K ct(g) = K`: expanding the product leaves `K + (s + c(s) + c(s) s a) w c(u)ᵀ K`, and the
coefficient vanishes because `c(δ) δ = 1`. By the matrix determinant lemma
(`Matrix.det_one_add_replicateCol_mul_replicateRow`),
`det g = 1 + s c(u)ᵀ w = 1 + (δ - 1) = δ`.

## Provenance

These are the standard facts that a nondegenerate Hermitian form over a quadratic extension
has an anisotropic vector and that its unitary group maps onto the norm-one elements by the
determinant (via a unitary reflection). In the proof of Landherr's theorem they produce, at
a nonsplit completion, a local solution of `y = w τ(w)` whose reduced norm is one.
