# A quantitative compact Dirac limit for real scalar principal series

Module `Langlands.Global.RankinSelberg.RealStandardCompactDirac`, namespace
`Langlands.Global.RankinSelbergGlobal.RealStandardCompactDirac`.

The module states that the scalar minimal principal series of `GL_{r+1}(ℝ)`, for every list
of `r + 1` real characters, contains a compact-finite vector whose rescaled translates by a
positive diagonal one-parameter family tend to the Dirac mass at the identity coset, in the
compact picture, with an explicit power rate against Lipschitz tests. The module states this
assertion and does not prove it. Besides the definitions it proves three short lemmas that fix
the conventions: the sign character is the restriction of the principal-series character, the
compact function of a standard vector is covariant for it, and the compact function of
`b R(g) f` is `k ↦ b f(k g)`.

## Conventions

`n = r + 1`. `G = GL_n(ℝ)` is the Library's `Langlands.GeneralLinear n ℝ`, and `K = O(n)` is
`Matrix.unitaryGroup (Fin n) ℝ`, the group on which the compact Banach completion
`RealStandardCompactBanach.Carrier n ds` (module `RealStandardCompactBanachAction`) lives.
Positions are `i = 0, …, n - 1`. A list `cs : List RealCharacterData` of length `r + 1` gives
the list of character blocks `ds = cs.map RealBlock.character`, of rank `r + 1`. Its standard
module `realStandardModule (r + 1) ds` is the smooth principal series of the position
characters `χᵢ` (the characters of `cs`): smooth `f` on `G` with
`f(diag(a) u g) = ∏ᵢ χᵢ(aᵢ) |aᵢ|^((n-1)/2 - i) f(g)` for `u` upper unipotent. Matrix norms are
the row-sum operator norms of `Matrix.Norms.Operator`, the norms used by `unitHeight` in
`BanachModerateGrowth`.

## Definitions

* `signUnit : ℤˣ →* ℝˣ`: the real unit `±1` of an integer sign.
* `signMatrix : (Fin n → ℤˣ) →* O(n)`: `ε ↦ diag(ε₀, …, ε_{n-1})`. Its range is the diagonal
  sign subgroup `M`. `toUnits_signMatrix`: in `G` it is `Iwasawa.diagonalUnits` of the signs.
* `signCharacter ds ε = ∏ᵢ χᵢ(εᵢ)`, with `χᵢ = realPositionCharacter ds i`: the sign character
  `χ` of `M` determined by the inducing characters.
* `IsSignCompatible ds ψ`, for `ψ : C(O(n), ℂ)`: `ψ(m k) = χ(m)⁻¹ ψ(k)` for every
  `m = signMatrix ε` and `k ∈ O(n)`.
* `IsMatrixLipschitz L ψ`: `‖ψ(k) - ψ(l)‖ ≤ L ‖k - l‖` for all `k, l ∈ O(n)`, the distance on
  `O(n)` being the one inherited from the row-sum operator norm of real matrices.
* `haarPairing φ ψ = ∫_{O(n)} φ(k) ψ(k) dk`, the bilinear pairing for the Haar probability
  measure `RealPrincipalSeriesHilbert.haarOrthogonal n` (module
  `RealPrincipalSeriesCompactAverages`).
* `compactFunction ds b g f`, for `f` in the real standard module: the continuous function on
  `O(n)` underlying `b • R(g)(embed ds f)`, where `R` is the jointly continuous action
  `RealStandardCompactBanach.representation ds` on the compact Banach completion and `embed ds`
  the inclusion of smooth standard vectors.

## Proved lemmas

* `principalSeriesCharacter_sign`: at a diagonal sign matrix the Library's
  `principalSeriesCharacter ℝ n (realPositionCharacter ds)` equals `signCharacter ds ε`, because
  `|±1| = 1` kills the modulus factor.
* `compactRestriction_signMatrix_mul`: for every `f` in `realStandardModule n ds`,
  `f(m k) = χ(m) f(k)` on `O(n)`. This is the principal-series equivariance with `u = 1`.
  So the compact function of a standard vector carries the sign `χ` on the left, and its
  product with a compatible test is left `M`-invariant.
* `compactFunction_apply`: `compactFunction ds b g f k = b f(k g)`, by `representation_embed`.

## The statement

`RealStandardCompactDiracStatement` is the proposition: for every `r : ℕ` and every
`cs : List RealCharacterData` with `cs.length = r + 1`, writing `ds = cs.map RealBlock.character`,
there exist

* a vector `ξ` of `realStandardModule (r + 1) ds` that is compact-finite, that is,
  `ξ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ (r + 1))` (by
  `realStandardCompactFinite`, these are the compact-finite smooth vectors of the compact
  Banach representation);
* real constants `C > 0` and `δ > 0` and an exponent `N : ℕ`;
* functions `a : ℝ → Fin (r + 1) → ℝˣ` and `b : ℝ → ℂ`,

such that for every real `t ≥ 1`, with `a_t = Iwasawa.diagonalUnits (a t)`:

1. every entry `a t i` is positive, so `a_t` is a positive diagonal element of `G`;
2. `unitHeight a_t ≤ C t^N`, where `unitHeight g = max(1, ‖g‖, ‖g⁻¹‖)` for the row-sum
   operator norm;
3. `‖b t‖ ≤ C t^N`;
4. for every `ψ : C(O(r+1), ℂ)` with `IsSignCompatible ds ψ` and every `L ≥ 0` with
   `IsMatrixLipschitz L ψ`,

   `‖haarPairing (compactFunction ds (b t) a_t ξ) ψ - ψ(1)‖ ≤ C t^(-δ) (‖ψ‖ + L)`,

   where `‖ψ‖` is the sup norm. By `compactFunction_apply` the pairing is
   `∫_{O(r+1)} b_t ξ(k a_t) ψ(k) dk`.

The seed `ξ`, the constants `C`, `δ`, `N` and the families `a`, `b` depend only on `r` and
`cs`, not on `t`, `ψ` or `L`. Every parity and every complex exponent of the characters is
allowed; the inducing data need not be unitary or spherical. A Lipschitz constant for another
norm on matrices gives the same assertion with a different `C`, since all norms on real
`n × n` matrices are equivalent.

## Source and derivation

Source: J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
arXiv:0812.1684v3 (published in Israel J. Math. 199 (2014), 45–111), Appendix A, §12.1.2–§12.1.4,
pp. 53–60 (the arXiv page numbers coincide with the PDF pages); the Library's literature
source `bernstein-kroetz-2014-smooth-frechet-globalizations-arxiv-v3`. There `G` is a real
reductive group and the representation is a spherical principal series `H_λ = L²(M\K)`.
§12.1.2 introduces the noncompact model on the opposite unipotent group `N̄` and the scaling
`[π_λ(a)f](n̄) = a^(λ+ρ) f(a⁻¹ n̄ a)`. §12.1.3 constructs, from a `K`-spherical
finite-dimensional representation `σ`, the `K`-finite function `f_σ` on `M\K` that vanishes
exactly off the big cell and decays polynomially to any order on `N̄` (Lemma 12.1, p. 56).
§12.1.4 forms `ξ = ξ_σ`, the elements `a_t = exp(log t · Y)` with `α(Y) ≥ 1` for every
positive root, and proves Theorem 12.2 (pp. 57–60) by splitting the coefficient integrals
into a far part (estimate (12.2)) and a near part (mean value estimate (12.3)).

The statement of this module is the special case `G = GL_n(ℝ)`, transcribed from `K`-types to
Lipschitz tests and extended from the spherical sector to every sign character of `M`. It is
not a statement of the paper. The following paper argument explains why it holds, with
`δ = 1`.

Notation: `B` is the upper triangular subgroup, `N̄` the lower unipotent group with Haar
measure `dX`, `ρᵢ = (n - 1)/2 - i`, `λᵢ` the exponent of `χᵢ`, and `ã^μ = ∏ ãᵢ^(μᵢ)` for
positive diagonal `ã`. Each `X ∈ N̄` factors uniquely as `X = u ã(X) κ(X)` with `u` upper
unipotent, `ã(X)` positive diagonal and `κ(X) ∈ K` (Gram–Schmidt), and these factors are
smooth in `X`.

1. **Integration formula.** For continuous left `M`-invariant `F` on `K`,
   `∫_K F(k) dk = c ∫_{N̄} ã(X)^(2ρ) F(κ(X)) dX` with a constant `c > 0`. This is the transfer
   between the compact and noncompact models used in BK §12.1.2.
2. **The pairing in the noncompact model.** For `F(k) = ξ(k a) ψ(k)` the left sign `χ` of `ξ`
   (`compactRestriction_signMatrix_mul`) cancels the inverse sign `χ⁻¹` of the compatible test,
   so `F` is left `M`-invariant. Since `ξ(κ(X) a) = ã(X)^(-λ-ρ) ξ(X a)`, the formula of step 1
   gives `∫_K ξ(k a) ψ(k) dk = c ∫_{N̄} ξ(X a) Ψ(X) dX`, where `Ψ(X) = ã(X)^(ρ-λ) ψ(κ(X))` is the
   noncompact model of `ψ` in the dual series, and `Ψ(1) = ψ(1)`.
3. **Scaling.** Take `a_t = diag(t^(n-1), t^(n-2), …, 1)`, so `α(Y) ≥ 1` for every positive
   root as in BK §12.1.4. The substitution `X ↦ a_t X a_t⁻¹`, of Jacobian `a_t^(-2ρ)`, and
   `ξ(a_t X) = a_t^(λ+ρ) ξ(X)` give BK's identity
   `∫_K ξ(k a_t) ψ(k) dk = c a_t^(λ-ρ) ∫_{N̄} ξ(X) Ψ(a_t X a_t⁻¹) dX`.
   The entry `(i, j)`, `i > j`, of `a_t X a_t⁻¹` is `t^(j-i) X_ij`, so
   `‖a_t X a_t⁻¹ - 1‖ ≤ t⁻¹ ‖X - 1‖` for `t ≥ 1`; this is BK's `‖Ad(a_t)⁻¹ X‖ ≥ t ‖X‖`.
4. **Normalization.** With `I_ξ = ∫_{N̄} ξ(X) dX ≠ 0` (step 7) put
   `b_t = (c a_t^(λ-ρ) I_ξ)⁻¹`. Then
   `b_t ∫_K ξ(k a_t) ψ(k) dk - ψ(1) = I_ξ⁻¹ ∫_{N̄} ξ(X) (Ψ(a_t X a_t⁻¹) - Ψ(1)) dX`.
   Here `unitHeight a_t = t^(n-1)` and `|b_t| = |c I_ξ|⁻¹ t^(-Re ∑ᵢ (n-1-i)(λᵢ-ρᵢ))`, both
   polynomial in `t`.
5. **The chart calculation with a Lipschitz test.** The maps `X ↦ κ(X)` and
   `X ↦ ã(X)^(ρ-λ)` are smooth with `κ(1) = 1` and `ã(1) = 1`, so on `‖X - 1‖ ≤ 1` they
   satisfy `‖κ(X) - 1‖ ≤ C ‖X - 1‖` and `|ã(X)^(ρ-λ) - 1| ≤ C ‖X - 1‖`. Hence
   `|Ψ(X) - Ψ(1)| ≤ |ã(X)^(ρ-λ) - 1| ‖ψ‖ + |ψ(κ(X)) - ψ(1)| ≤ C (‖ψ‖ + L) ‖X - 1‖` there.
   In BK this is estimate (12.3), where the mean value theorem and the gradient bound
   `C (1 + |τ|)` of the transferred `K`-type functions `D_τ^{i,j}` are used; for the test `ψ`
   the Lipschitz constant `L` takes the place of the gradient bound. Globally
   `|Ψ(X)| ≤ C ‖ψ‖ (1 + ‖X‖)^q` by the polynomial growth of `ã^(±1)`; this replaces the bound
   `|D_τ^{i,j}(X)| ≤ C (1 + ‖X‖)^(q₂)` in the estimate of `b¹_{i,j}(t)`.
6. **Near and far parts.** On `‖a_t X a_t⁻¹ - 1‖ ≤ 1` the integrand of step 4 is at most
   `C (‖ψ‖ + L) t⁻¹ |ξ(X)| ‖X - 1‖`. On the complement `‖X - 1‖ > t`, and the integrand is at
   most `C ‖ψ‖ |ξ(X)| (1 + ‖X‖)^q ≤ C ‖ψ‖ t⁻¹ |ξ(X)| (1 + ‖X‖)^(q+1)`, as in BK's estimate (12.2)
   of the far part. Both integrals converge once `|ξ(X)| ≤ C (1 + ‖X‖)^(-m)` with
   `m > q + 1 + dim N̄`, and the error is at most `C t⁻¹ (‖ψ‖ + L)`. No choice `t = t(τ)` as in
   BK is needed, because a fixed test has a fixed Lipschitz constant, whereas the gradients of
   `D_τ^{i,j}` grow with `τ`.
7. **The seed in the sign sector.** BK's `f_σ` is `M`-invariant, so it only serves the
   spherical sector. For the sign character `χ`, let `Δ_j` be the bottom-right `j × j` corner
   minor, `Q = Δ_1 ⋯ Δ_n`, and let `P = Δ_{j_1} ⋯ Δ_{j_s}` be a product of corner minors with
   `P(m k) = χ(m) P(k)`: left multiplication by `diag(ε)` multiplies `Δ_j` by
   `ε_{n-j} ⋯ ε_{n-1}`, and products of these tails realize every sign pattern. The seed is the
   principal-series vector with compact profile `P Q^(2m)`, which is compact-finite as a
   product of matrix coefficients (compare `RealBottomMinorProducts.coefficient_mem_kFiniteVectors`).
   On `K`, `|Δ_j| ≤ 1` because the squares of the minors in a row set sum to one
   (`RealBottomMinorProducts.sum_coefficient_sq`), so `|Q| ≤ 1`, with equality exactly on
   `M`. On `N̄`, `Δ_j(X) = 1` and `Δ_j(u ã κ) = (∏_{i ≥ n-j} ãᵢ) Δ_j(κ)`, so `Δ_j(κ(X))⁻¹` is
   the norm of the wedge product of the last `j` rows of `X`; that norm squared is at least
   `1 + ∑_{l < n-j} X_{n-j,l}²`. Hence `|Q(κ(X))|² ≤ ∏ᵢ (1 + ∑_{l<i} X_il²)⁻¹ ≤ (1 + ‖X - 1‖₂²)⁻¹`,
   and `ξ(X) = ã(X)^(λ+ρ) P(κ(X)) Q(κ(X))^(2m)` is bounded by `C (1 + ‖X‖)^(q' - 2m)` with `q'`
   independent of `m`: the analogue of Lemma 12.1(ii), with decay of any order away from the
   identity class. Since `ξ(1) = 1` and `-log |Q(κ(X))|²` has a nondegenerate minimum at
   `X = 1`, Laplace's method gives `I_ξ ≠ 0` for large `m`. This corresponds to BK's remark on
   p. 59 that `I_ξ ≠ 0` once `μ` is large.

The estimate is an input for polynomially controlled compact convolution on principal-series
vectors. This module does not state that application or the Casselman–Wallach theorem.
