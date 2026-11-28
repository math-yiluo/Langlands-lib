# Regular unitary elements at a place not split in the quadratic extension

Module: `Langlands.Algebra.CentralSimple.UnitaryRegularNonsplit`, namespace
`Langlands.CentralSimple.UnitaryPoints`.

## Polynomials with norm-one roots

- `reflect_prod_X_sub_C`: for a ring endomorphism `σ` of a commutative ring `R` and `vᵢ` with
  `vᵢ σ(vᵢ) = 1` (`i ∈ s`), `reflect |s| (∏ (X - vᵢ)) = (∏ (-vᵢ)) · σ(∏ (X - vᵢ))`. Induction on
  `s` with `reflect_mul`; each factor reflects to `1 - vᵢ X = (-vᵢ)(X - σ(vᵢ))`.
- `coeff_prod_X_sub_C_reciprocal`: hence `f = ∏_{i<n} (X - vᵢ)` satisfies
  `f_{n-i} = (-1)ⁿ (∏ vᵢ) σ(f_i)` for `i ≤ n`.

## Distinct norm-one elements

`exists_injective_prod_eq_add_two` and `exists_injective_prod_eq`: let `N` be an infinite set
of nonzero elements of a field, closed under products and inverses, `w ∈ N` and `n ≥ 1`. Then
`w` is a product of `n` distinct elements of `N`. For two factors choose `a ∈ N` outside the
finitely many values with `a ∈ T`, `w a⁻¹ ∈ T` or `a² = w`, and take `(a, w a⁻¹)`; more factors
are added one at a time, avoiding the earlier ones.

## Unitary diagonalizable matrices

Let `L` be a field, `c` a nontrivial involution of `L` (an `AlgebraInvolution R L` from
`Langlands.Shimura.Unitary.Involution`), `2 ≠ 0` in `L`, and `ρ` an involution of
`M_n(L)` with `ρ(a) = c(a)` on scalars.

- `involutionRingHom c`: `c` as a ring endomorphism.
- `exists_unitary_conj_diagonal`: there is an invertible `Q` with
  `X ρ(X) = 1` for `X = Q diag(v) Q⁻¹` whenever `vᵢ c(vᵢ) = 1` for all `i`. The Library's
  `exists_hermitianGram_of_matrixInvolution` writes `ρ(X) = H⁻¹ c(X)ᵀ H` with `c(H)ᵀ = H`;
  `Langlands.Sesquilinear.exists_congr_diagonal_of_hermitian` gives `P` with
  `Pᵀ H c(P) = diag(d)`. With `Q = c(P)` one has `c(Q)ᵀ = Pᵀ`, and a direct computation gives
  `c(X)ᵀ H X = H`, so `ρ(X) X = 1` and `X ρ(X) = 1`.
- `aeval_diagonal`: `p(diag(v)) = diag(p(vᵢ))`; `conjAlgHom Q` is conjugation by `Q` as an
  `L`-algebra map (`conjAlgHom_apply`, `conjAlgHom_injective`).

## Scalars

- `algebraMap_eq_tensorEquiv_centerMap`: in `(E ⊗[F] K) ⊗[E] B`, the scalar `ℓ` is
  `tensorEquiv (ψ (comm ℓ))`, where `comm : E ⊗[F] K → K ⊗[F] E` and `ψ = centerMap F E B K`.
- `centerConj_comm`: `comm` intertwines `conj ⊗ id` with `id ⊗ conj`.

## The main result

`exists_regular_unitary_of_isField`: let `K` be a field of characteristic zero with
`UnitaryInvolutionSplitting K` (`Langlands.Algebra.UnitaryInvolutionStatements`) such that
`E ⊗[F] K` is a field, `finrank E B = n²`, `z ∈ Eˣ`, and let `x₀` be a unitary point of
`K ⊗[F] B` with `relativeNorm x₀ = z ⊗ 1`. Then the conclusion of
`NumberFieldUnitaryRegularLocalStatement` holds with `K` in place of the completion. The
proof:

1. `L = E ⊗[F] K` is a field (`IsField.toField`), a quadratic extension of `K` through the
   right factor, with nontrivial `K`-automorphism `σ = conj ⊗ id`.
2. `A' = L ⊗[E] B` is central simple over `L`, and `τ' = tensorEquiv ∘ τ_K ∘ tensorEquiv⁻¹` is
   a unitary involution relative to `σ` (`algebraMap_eq_tensorEquiv_centerMap`,
   `baseChange_centerMap`). `UnitaryInvolutionSplitting K` gives `Φ : A' ≃ₐ[L] M_m(L)`, and
   `m = n` by dimension.
3. `exists_unitary_conj_diagonal` for `ρ = Φ τ' Φ⁻¹` gives `Q`.
4. `z z̄ = 1` (`mul_conjugation_eq_one`), and the norm-one elements `{v | v σ(v) = 1}` of `L`
   form an infinite set: `t ↦ (ω + t)/(σ(ω) + t)` (`t ∈ K`, `σ(ω) ≠ ω`) is injective.
   `exists_injective_prod_eq` gives distinct `vᵢ` of norm one with `∏ vᵢ = z ⊗ 1`.
5. `x = tensorEquiv⁻¹ (Φ⁻¹ (Q diag(v) Q⁻¹))` and `f = comm(∏ (X - vᵢ))`. Then `x τ_K(x) = 1`;
   `f` is monic of degree `n`; `coeff_prod_X_sub_C_reciprocal` gives the coefficient
   relations; `f(x)` and `f'(x)` are the images of `f(diag v) = 0` and of the unit
   `f'(diag v)` (`f` is separable because the `vᵢ` are distinct); and `∑ ψ(cᵢ) xⁱ = 0` makes
   the polynomial `∑ cᵢ Xⁱ` of degree `< n` vanish at the `n` distinct `vⱼ`, so `c = 0`.

## Provenance

Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.6, Step 1, printed
pp. 79–80 (PDF pp. 85–86), source `kneser-1969-galois-cohomology-classical-groups`: at a place
not split in the quadratic extension, the local algebra is a matrix algebra in which the
involution is the adjoint of a Hermitian form, and a regular unitary matrix of prescribed
determinant exists. Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), proof
of Theorem 6.28, printed pp. 363–364 (PDF pp. 373–374), source
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, relations (6.44). The diagonal
matrix with distinct norm-one entries is the construction of Kneser's argument; the
distinct-factor lemma and the parametrization of norm-one elements are internal.
