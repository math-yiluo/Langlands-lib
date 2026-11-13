# The conductor lower bound and scaled identity from the spherical functional equation

Author: Worker 5077. Module
`Langlands.Representation.Conductor.ConductorMinimalityReduction`. Its main
theorem is

```lean
theorem Langlands.Conductor.conductorMinimalityStatement_of_sphericalFunctionalEquation
    (hFE : SphericalLaurentFunctionalEquationStatement.{uF, uV})
    (hinj : Whittaker.MirabolicRestrictionInjectivityStatement.{uF, uV}) :
    ConductorMinimalityStatement.{uF, uV}
```

It is a conditional reduction with internal provenance: it proves the published
`ConductorMinimalityStatement` ([statement](ConductorMinimalityStatement.md))
from two statements that it does not prove,
[`SphericalLaurentFunctionalEquationStatement`](SphericalLaurentFunctionalEquationStatement.md)
(the corank-one functional equation against `W(g; x; ψ̄)` with its
convergence and pole bound) and the published
`Langlands.Whittaker.MirabolicRestrictionInjectivityStatement`. It therefore
does not by itself prove `ConductorMinimalityStatement`; the universes `uF`,
`uV` of the three statements agree, and every nonarchimedean local field is
covered. The axioms are `propext`, `Classical.choice` and `Quot.sound`.

The module's one definition is `Langlands.Conductor.degreeIntegral` (section
`Degree` below), the degree-`d` Laurent coefficient of the corank-one integral;
every other declaration is a theorem.

## Source

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), end of the proof of
Theorem (5.1), printed pages 213–214 (registered `jpss-1981-conductor`, PDF pages
15–16). The source shows that `Ξ(W₁)` is a polynomial `P` by the support of
`H(0)`-invariant vectors, that the corresponding transform of the translated
dual function is a polynomial `Q`, and compares them through (4.2)(7):
`(X₁⋯X_(r-1))^u Q(q⁻¹X⁻¹) = C^(r-1) q^(-u(r-1)) (X₁⋯X_(r-1))^m P(X)`. The Lean
proof uses the same three inputs but compares exponents of `q^(-s)` for each
fixed Satake parameter `x`, without the translate by
`diag(ϖ^(-u), …, ϖ^(-u), 1)`: the bound on the dual side comes directly from the
invariance of the dual function under `1 + 𝔭^u E_(n,n+1)`. The non-vanishing
`W₁ ≠ 0 ⇒ Ξ(W₁) ≠ 0` that the source uses tacitly ("ce qui est absurde") is
supplied by mirabolic restriction injectivity.

## Laurent expansions (section `Laurent`)

- `eq_zero_of_hasSum_spectralPoint`: if `c : ℤ → ℂ` vanishes below some `d₀`
  and `∑_d c_d (q^(-s))^d = 0` for every real `s > a` (with `q > 1`), then
  `c = 0`. The substitution `X = q^(-s)` turns the real half-line into an
  interval `(0, q^(-a))`, and the published `eq_zero_of_hasSum_int_eq_zero`
  ([`EssentialRestrictionUniqueness`](EssentialRestrictionUniqueness.md))
  applies.
- `hasSum_polynomial_mul`: if `∑_d e_d X^d = S` (as `HasSum`, `X ≠ 0`) then for a
  polynomial `D`, `∑_d (∑_(j ∈ supp D) D_j e_(d-j)) X^d = D(X) S`. Each monomial
  shifts the series; the finite sum of these `HasSum` statements is taken.
- `hasSum_laurentEval`: a Laurent polynomial `Q` is the sum of its monomials,
  `∑_d Q_d x^d = laurentEval x Q`, by induction on `Q`.

## Level subgroups (section `Matrices`)

- `adjacentUnit_val_apply`, `adjacentUnit_val_inv`: the entries of
  `1 + y E_(i,i+1)` and its inverse `1 - y E_(i,i+1)`.
- `inverseTranspose_rankInclusion'`: `ᵗdiag(B, 1)⁻¹ = diag(ᵗB⁻¹, 1)`.
- `rankInclusion_torus`: `diag(ϖ^λ, 1) = ϖ^(λ, 0)`.
- `inverseTranspose_mem_integralSubgroup'`: `GL_(r+1)(O)` is stable under
  inverse transpose.
- `exists_mem_maximalIdeal_pow`: `ϖ^a z ∈ 𝔭^a` for integral `z`, using the
  published `maximalIdeal_pow_eq_span_jacquetUniformizer`.
- `adjacentUnit_last_mem_levelSubgroup`: `1 + z E_(n,n+1)` (integral `z`) lies in
  `levelSubgroup F (n + 1) a` for every `a`; its last row is `(0, …, 0, 1)`.
- `inverseTranspose_adjacentUnit_last_mem_levelSubgroup`: the inverse transpose
  of `1 + ϖ^a z E_(n,n+1)` is `1 - ϖ^a z E_(n+1,n)`, whose last row is
  `(0, …, 0, -ϖ^a z, 1)`, so it lies in `levelSubgroup F (n + 1) a`. Membership
  is checked with the published `mem_levelSubgroup_of_entries`.

## Support on the torus (section `Support`)

`torus_support_of_invariant`: let `ψ'` have conductor `O`, `ϖ` be a uniformizer,
`b : ℕ`, and `W` a `ψ'`-Whittaker function on `GL_(n+2)` whose restriction to
`diag(GL_(n+1), 1)` is right `GL_(n+1)(O)`-invariant and which is right
invariant under `1 + ϖ^b z E_(n,n+1)` for all integral `z`. If
`W(diag(ϖ^λ, 1)) ≠ 0` then `λ` is antitone (dominant) and `λ_n ≥ -b`.
Dominance is the published `UnramifiedWhittaker.eval_torus_eq_zero_of_not_antitone`,
with the nontriviality of `ψ'` on `ϖ⁻¹ O` obtained from the conductor exactly
as in the published `torus_eq_zero_of_not_antitone_of_restriction`. For the last
exponent, conjugation (published `torus_inv_conj_adjacentUnit`) gives
`(1 + ϖ^(λ_n) y E_(n,n+1)) diag(ϖ^λ, 1) = diag(ϖ^λ, 1) (1 + y E_(n,n+1))`; with
`y = ϖ^b z` the left equivariance and right invariance give
`ψ'(ϖ^(λ_n + b) z) = 1` for all integral `z`, so `ϖ^(λ_n+b) ∈ O` by the conductor
condition, that is `λ_n + b ≥ 0`.

`quotientExponent_support_of_integrand_ne_zero` transfers this to every point of
`N_(n+1) \ GL_(n+1)`: writing a representative as `u ϖ^λ k`, the integrand is a
multiple of `W(diag(ϖ^λ, 1))`, so a nonzero integrand forces the support
condition on the quotient exponent. `sum_ge_of_antitone` gives
`Σ λ_i ≥ (n + 1) λ_n` for antitone `λ`.

## Degree coefficients (section `Degree`)

`degreeIntegral h' W W' d` is the degree-`d` integral at `s = 0`, the
coefficient of `(q^(-s))^d` in the published `hasSum_corankOneIntegral`.

- `degreeIntegral_eq_zero_of_lt`: under the support condition with bound `b`,
  the coefficients vanish for `d < -(n + 1) b`, since the integrand vanishes
  on those strata.
- `degreeIntegral_zero_eq`: with `b = 0` and the spherical test
  `W(g; x; ψ̄)`, the degree-zero coefficient is
  `μ(N \ N GL_(n+1)(O)) · W(1)`. On degree zero the support condition leaves
  only `λ = 0`, the cell `sphericalCell h.uniformizer 0`, where the integrand is
  `W(1) · W(1; x; ψ̄) · |det k|^(-1/2) = W(1)`.

## Exponent bounds (section `Numerator`)

- `laurent_coeff_of_forward`: if `f(s) = ∑_(d ≥ 0) e_d (q^(-s))^d` for large
  real `s`, `f` continues to `R`, and `Q = D R` with `D(0) = 1`, then `Q` has no
  negative exponents and `Q_0 = e_0`. On a half-line,
  `Q(X) = D(X) f(s)` (published `laurentEval_eq_of_laurentToRatFunc_eq`), both
  sides are expanded as Laurent series in `X = q^(-s)`, and their coefficients
  agree by `eq_zero_of_hasSum_spectralPoint`.
- `laurent_coeff_of_dual`: if the dual integral is
  `∑_(d ≥ -B) ẽ_d (q^(-s))^d` for large real `s`, continues to `Rd`, and the
  normalized functional equation relates `Rd` and `R` with epsilon monomial
  `c q^(-Ms)`, then every exponent `k` of `Q` satisfies `k ≤ B - M`. For large
  real `s'`, the equation at `s = 1 - s'` (avoiding the finitely many real
  `s'` with `R.denom(q^(-(1-s'))) = 0`, published
  `finite_reflected_spectralPoint_roots`) reads
  `Dd(X') fd(s') = ζ^e c X^M Q(X)` with `X = q⁻¹ X'⁻¹`. Expanding the right side
  in `X'` gives coefficients `ζ^e c Q_(-M-d) q^d`, the left side has
  coefficients vanishing below `-B`; comparing coefficients gives the bound.

## Assembly (section `Assembly`)

`prod_comp_coeff_zero` and `laurentToRatFunc_eq_mul_essentialFactor` record
`(∏ P(x_i X))(0) = 1` and `Q = ∏ P(x_i X) · (Q ∏ P(x_i X)⁻¹)`.

In `conductorMinimalityStatement_of_sphericalFunctionalEquation`, fix the data
of the target and a vector `v` fixed by `levelSubgroup F (n + 1) u`, and apply
`hFE` to the same data.

- The forward function `v` satisfies the support condition with `b = 0`: its
  restriction is `GL_(n+1)(O)`-invariant (published
  `isIntegralInvariantOnRestriction_of_mem_levelFixedVectors`) and
  `1 + z E_(n,n+1)` lies in the level subgroup.
- The dual function `ṽ = firstDualFunction ψ (n + 1) v.val`,
  `ṽ(g) = v(w₀ ᵗg⁻¹)`, is a `ψ̄`-Whittaker function (`ψ̄` has conductor `O`, published
  `hasIntegerConductor_scale_neg_one`) satisfying the support condition with
  `b = u`: `ṽ(g h) = v(w₀ ᵗg⁻¹ ᵗh⁻¹)` and the inverse transposes of
  `diag(k, 1)` and of `1 + ϖ^u z E_(n,n+1)` lie in the level subgroup.
- For each `x`, `hFE` gives convergence, `Q`, `Rdual` and the functional
  equation with `D = ∏ P(x_i X)`, `Dd = ∏ Pdual(x_i⁻¹ X)`,
  `M = (n + 1) m`. The published `hasSum_corankOneIntegral` (for `h` and for
  the dual normalization `h.scaleNegOne`) expands both integrals. Hence
  `Q_k = 0` for `k < 0`, `Q_0 = μ(cell 0) v(1)`, and
  `Q_k ≠ 0 ⇒ k ≤ (n + 1)(u - m)`.
- **Lower bound.** If `v ≠ 0` and `u < m`, then `Q = 0` for every `x`, so every
  corank-one integral of `v` against `W(·; x; ψ̄)` vanishes on a real half-line.
  The published `eq_zero_on_restriction_of_integrals_eq_zero` makes `v` vanish on
  `diag(GL_(n+1), 1)`, the published `whittaker_mirabolic_eq_of_levi_eq` on the
  mirabolic subgroup, and `hinj` applied to a preimage of `v` in `V` gives
  `v = 0`, a contradiction.
- **Scaled identity.** If `u = m`, then `Q` is the constant
  `C = μ(cell 0) · v(1)`, independent of `x`, so the forward integral continues
  to `C • essentialFactor P x`; convergence is part of `hFE`.

## Remaining obligations

To prove `ConductorMinimalityStatement` outright, both hypotheses must be
proved over every nonarchimedean local field: mirabolic restriction injectivity
(proof task `20fcd75c-eb88-415e-83c0-7d767ae2e3a6`) and the spherical
functional equation, which contains JPSS 1983 Theorems (2.7) and (3.1) for
unramified principal series.

## Imports

`ConductorMinimalityStatement`, `SphericalLaurentFunctionalEquationStatement`,
`Whittaker.MirabolicRestrictionInjectivityStatement`, and the published helpers
`Conductor.EssentialRestrictionUniqueness`, `Conductor.EssentialDualSetup`,
`Conductor.SphericalCompact`, `RankinSelberg.HighlyRamified.LastRowAgreement` and
`RankinSelberg.LaurentEvaluation`.
