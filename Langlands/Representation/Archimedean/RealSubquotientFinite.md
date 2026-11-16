# Gelfand elements, finiteness and nilpotency

Module: `Langlands.Representation.Archimedean.RealSubquotientFinite` (namespace
`Langlands.Archimedean.RealSubquotient`).

This is a helper module for the proof of `RealPrincipalSeriesSubquotientStatement`; see
`RealPrincipalSeriesSubquotientProof.md`. In Wallach, *Real Reductive Groups I*, 3.5.10, the
nilpotency step uses the Harish-Chandra isomorphism `q(Z(𝔤)) = U(𝔥)^W` (Theorem 3.2.3) and the
`W`-symmetrized characteristic polynomial `det(T - p_γ(u))`. This module replaces those with
Gelfand's central elements, power sums and the determinant trick. Throughout, `τ` is continuous with
derivative `D`, and `d > 0` where needed.

## Gelfand's central elements

- `Cgel n l = tr(E^l)`, where `E` is the matrix of generators
  `RealJacquetFiniteGeneration.gen n`. It is central (`Cgel_mem_center`, from the Library's
  `trace_gen_pow_mem_center`), lies in `U_l` (`Cgel_mem_degreeFiltration`), and its symbol is
  `tr(X^l)` for the generic matrix `X` (`symbol_Cgel`, via `gen_pow_mem_and_symbol`). The
  diagonal restriction of that symbol is the power sum `p_l` (`diagRes_symbol_Cgel`).
- `xiPoly τ z = Q(z, e₀)₀` (zero if `d = 0`). `Q_central`: for central `z`,
  `Q(z, v)ᵢ = xiPoly τ z · vᵢ`. `xiPoly_top`: for `z ∈ U_N`, `xiPoly τ z` has degree `≤ N` and
  top part `diagRes(σ_N(z))`. In particular (`xiPoly_Cgel_top`), `ξ_l := xiPoly τ (Cgel n l)`
  has degree `≤ l` with degree-`l` part `p_l`.
- `Bsub τ`: the `K`-invariant matrices (`InB τ`) form a subalgebra (`mem_Bsub`). Scalar
  diagonal matrices of central elements lie in it (`diagonal_mem_Bsub`).
- `chat_add`, `chat_diagonal_central` (`ĉ(diag(z)) = diag(xiPoly τ z)`), and the evaluation
  `zetaC`/`zeta` of polynomials `r ∈ ℂ[X_0, X_1, …]` in the Gelfand elements (through the centre,
  which is commutative). `chat_diagonal_zeta`: `ĉ(diag(zeta r)) = diag(phiGel τ r)`, where
  `phiGel τ = aeval (l ↦ ξ_l)`.

## Finiteness over the Gelfand polynomials

- `boxSet n`: the exponents `β` with all `βᵢ < n`. `SpanBox ξ`: the polynomials
  `∑_{β ∈ box} aeval ξ (g_β) · a^β`. It is closed under sums, scalar multiples and multiplication
  by `aeval ξ r` (lemmas `SpanBox.*`), and contains the box monomials.
- `mem_spanBox`: suppose `ξ_l` has degree `≤ l` and degree-`l` part `p_l` for `l ≥ 1`. Then
  every polynomial lies in `SpanBox ξ`. The proof is by induction on degree. A monomial with an
  exponent `≥ n` lies in the span of the products `a^γ p_l` with `l ≥ 1`, by the Library's
  `RealJacquetFiniteGeneration.monomial_mem_powerSumSpan`. Replace `p_l` by `ξ_l` minus
  lower-order terms (`sub_homogeneousComponent_eq_sum`).
- `finite_fibre`: under the same hypothesis, `{a : ξ_l(a) = λ_l for all l}` is finite. Write
  `aᵢ^k = ∑_{β ∈ box} aeval ξ (g_{kβ}) · a^β` (`mem_spanBox`). On the fibre this becomes
  `aᵢ^k = ∑_β g_{kβ}(λ) · a^β` (`eval_aeval_of_fibre`). The `|box| + 1` coefficient vectors
  `(g_{kβ}(λ))_β`, `k ≤ |box|`, are linearly dependent. A dependence `∑ₖ tₖ (g_{kβ}(λ))_β = 0`
  gives a nonzero polynomial `∑ₖ tₖ Xᵏ`, independent of `a`, with root `aᵢ` at every point of
  the fibre. So each coordinate takes finitely many values.

## Determinant trick and nilpotency

- `exists_monic_matrix_poly`: let `A` be a finite commutative `R`-algebra and `Y` a `d × d`
  matrix with entries in `J·A`. Then `∑ₖ pₖ Yᵏ = 0` for a monic `p` with `pₖ ∈ J^{deg p - k}`.
  It is Mathlib's
  `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero` (Cayley–Hamilton
  for finite modules) applied to left multiplication by `Y` on `Mat_d(A)`.
- `act_add`, `act_zero'`, `act_sum`, `act_diagonal` (`diag(z)` acts by `P(z)`), `chat_one`,
  `chat_pow` (`ĉ(xᵏ) = ĉ(x)ᵏ` for `K`-invariant `x`, by `chat_mul`), `chat_sum`,
  `entries_pow_mem`.
- `exists_pow_act_eq_zero` (**nilpotency**): let the Gelfand elements act on a
  `(𝔤𝔩_n(ℝ), O(n))`-module `M` by scalars `λ_l`, let `T₀` be a `K`-intertwiner from `τ` into
  `M`, and let `x ∈ Bsub τ` with `ĉ(x)(a) = 0` at every `a` of the fibre `{ξ_l(a) = λ_l}`. Then
  `x^m · T₀ = 0` for some `m`. The entries of `ĉ(x)` lie in the radical of the ideal
  `I = (ξ_l - λ_l)` (Nullstellensatz, `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`), so the
  entries of `Y = ĉ(x)^N` lie in `I`. `ℂ[a]` is finite over `ℂ[X_l]` through `phiGel`
  (`mem_spanBox`), and `I` is contained in the extension to `ℂ[a]` of the kernel `J` of `r ↦ r(λ)`. The determinant trick
  gives a monic `p`, and `w = ∑ₖ diag(zeta pₖ) x^{Nk}` is `K`-invariant with `ĉ(w) = 0`, so
  `w · T₀ = 0` by `act_eq_zero_of_chat_eq_zero`. Since `zeta pₖ` acts by `pₖ(λ)`, which is `0`
  for `k < deg p` and `1` for the leading coefficient, this says `x^{N·deg p} · T₀ = 0`.
