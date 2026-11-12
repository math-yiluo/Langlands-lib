# Polynomials in operators and the Rayleigh bound

Module: `Langlands.Automorphic.CuspidalAdmissible.PolynomialRayleigh`.
Provenance: internal. These are elementary linear-algebra facts used in the proof of joint
admissibility of unitary cuspidal realizations (an input of the cuspidal contragredient
existence theorem). They follow no particular source; the Rayleigh bound is the standard
estimate of a quadratic form by the spectral radius on a finite-dimensional invariant
subspace.

All declarations are in the namespace `Langlands.Automorphic.CuspidalAdmissible`.

## Calculus of `aeval` (any complex vector space `V`)

- `aeval_restrict_apply A hW p w`: for an `A`-invariant subspace `W`, the polynomial `p`
  in the restriction `A|_W`, applied to `w ∈ W`, equals `p(A) w`. Induction on `p`
  (`Polynomial.induction_on`); the monomial step writes `C a * X^(k+1) = C a * X^k * X`.
- `aeval_intertwine B h p v`: if a linear map `B : V → W` satisfies `B (A v) = A' (B v)` for
  all `v`, then `B (p(A) v) = p(A') (B v)`. Same induction.
- `aeval_apply_commute`: the special case `W = V`, an operator `B` commuting with `A`.
- `aeval_mem_of_stable`: an `A`-stable subspace is `p(A)`-stable (via
  `aeval_restrict_apply`).
- `aeval_charpoly_restrict_apply`: for a finite-dimensional `A`-invariant subspace `W`, the
  characteristic polynomial of `A|_W` kills every vector of `W` (Cayley–Hamilton,
  `LinearMap.aeval_self_charpoly`, transported by `aeval_restrict_apply`).
- `exists_aeval_apply_eq_zero`: hence a vector lying in a finite-dimensional `A`-invariant
  subspace is killed by a nonzero (monic) polynomial in `A`.

## Root bound and Rayleigh bound (complex inner product space `E`)

- `rootBound q : ℝ≥0` is the supremum of `‖z‖` over the roots `z` of `q` (with
  multiplicity, `q.roots`), and `0` if there are none. `nnnorm_le_rootBound`: every root of
  a nonzero `q` has norm at most `rootBound q`.
- `evalAt T x : ℂ[X] →ₗ[ℂ] E` is `p ↦ p(T) x`; `cyclicSpan T x N` is the image of the
  polynomials of degree `< N` (`degreeLT`), a finite-dimensional subspace.
- If `q` is monic and `q(T) x = 0`, then (`aeval_mem_cyclicSpan`) every `p(T) x` lies in
  `cyclicSpan T x (natDegree q)`, by division with remainder by `q`; in particular `x`
  and `T`-images of the span stay in it (`mem_cyclicSpan_self`, `apply_mem_cyclicSpan`),
  and `q(T)` kills the whole span (`aeval_eq_zero_of_mem_cyclicSpan`).
- `norm_inner_self_le_of_monic`: if `T` is symmetric, `q` monic and `q(T) x = 0`, then
  `‖⟪T x, x⟫‖ ≤ rootBound q · ‖x‖²`. Proof: restrict `T` to the cyclic span `Z`
  (symmetric, `IsSymmetric.restrict_invariant`), take its orthonormal eigenvector basis
  (`IsSymmetric.eigenvectorBasis`). Each eigenvalue `λ` has an eigenvector in `Z`, which
  `q(T)` kills, so `q(λ) = 0` (`Module.End.aeval_apply_of_hasEigenvector`) and
  `|λ| ≤ rootBound q`. Expanding `⟪T x, x⟫ = ∑ λ_i |x_i|²` in the eigenbasis (Parseval,
  `OrthonormalBasis.repr`) gives the bound.
- `norm_inner_self_le_of_aeval`: the same bound for any nonzero `q`, by normalizing `q`
  to the monic `C (lead q)⁻¹ * q`, which has the same roots.
