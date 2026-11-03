# Truncated Taylor expansion along a section

This module is part of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
It concerns an `A`-algebra `S` with an `A`-algebra section `σ : S →ₐ[A] A`, kernel
`J = RingHom.ker σ`, and coordinates `t : Fin d → S` with `σ (t i) = 0`. It compares the truncated
polynomial module `A[T₁,…,T_d]/(T)^k` with `S/J^k`.

## Definitions

- `Mon d k`: exponent vectors `α : Fin d →₀ ℕ` of total degree `< k`.
- `tpow t α`: the monomial `t ^ α = aeval t (monomial α 1)`.
- `theta σ t k : (Mon d k →₀ A) →ₗ[A] S ⧸ J ^ k`: the linear map sending the basis vector of `α`
  to the class of `t ^ α`.
- `restr h`: for `k ≤ k'`, restriction of coefficient vectors from degree `< k'` to degree `< k`.
- `taylor σ t hθ k : S →ₗ[A] (Mon d k →₀ A)`: assuming every `theta σ t k` is bijective (`hθ`),
  the inverse of `theta` composed with the quotient map.
- `taylorCoeff σ t hθ α : S →ₗ[A] A`: the coefficient of `α` in `taylor σ t hθ (deg α + 1)`.

## Statements

- `aeval_mem_ker_pow`, `tpow_mem_ker_pow`: polynomials in `(T)^m` evaluate into `J^m`. In
  particular `t ^ α ∈ J ^ (deg α)`.
- `theta_restr`: `theta` is compatible with restriction and the projection `S/J^k' → S/J^k`.
- `exists_approx_step`, `exists_aeval_sub_mem`, `theta_surjective`: if
  `J ≤ span (range t) ⊔ J ^ 2`, every element of `S` is congruent modulo `J^m` to a polynomial
  in `t`, so `theta σ t k` is surjective.
- `aeval_monomial_sub_mem`: if `q i - X i ∈ (X)^2` for all `i`, then
  `q ^ α - X ^ α ∈ (X)^(deg α + 1)`.
- `theta_injective_of_lift`: suppose there is an `A`-algebra map
  `ψ : S ⧸ J^k → A[T]/(T)^k` with `ψ (t i) = q i` and `q i - X i ∈ (X)^2`. Then `theta σ t k` is
  injective.
- `theta_taylor`, `restr_taylor`, `taylor_apply`: basic properties of `taylor`. Every coordinate
  of `taylor k s` is a Taylor coefficient `taylorCoeff α s`.
- `mem_pow_smul_top_of_taylorCoeff`: for any `A`-module `N`, if all Taylor coefficients
  `(taylorCoeff α).rTensor N y` of `y ∈ S ⊗[A] N` vanish, then `y ∈ J^k • ⊤` for every `k`.

## Proofs

Surjectivity holds by induction on `m`. An element of `J^(m+1) = J^m * J` is approximated using
the approximations of the two factors. The base case writes an element of `J` as `∑ cᵢ tᵢ + z`
with `z ∈ J^2`, and replaces `cᵢ` by `σ cᵢ`.

Injectivity is a triangularity argument. Suppose `∑ c_α q^α ∈ (X)^k` and let `α₀` be an exponent
of minimal degree with `c_{α₀} ≠ 0`. The coefficient of `X^{α₀}` in the sum is `c_{α₀}`, because
`q^α - X^α` only has monomials of degree `> deg α`. This contradicts
`MvPolynomial.mem_pow_idealOfVars_iff'`.

The vanishing statement uses right exactness of `- ⊗ N`. It identifies `(S/J^k) ⊗ N` with
`(Mon d k →₀ A) ⊗ N ≅ Mon d k →₀ N` (`TensorProduct.finsuppScalarLeft`), whose coordinates are
the Taylor coefficients. It also uses that the image of `J^k ⊗ N` is contained in `J^k • ⊤`.

## Provenance

This is internal infrastructure for the 05FT proof, written by Worker 281. The identification of
`S/J^k` with truncated polynomials along a section in the smooth locus is standard; compare
the sketch in Stacks Remark 05FU.
