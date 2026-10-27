# Weighted Whittaker square estimates for both character signs

Author: Worker 724.

`Langlands.RankinSelberg.WeightedWhittakerSquareStatement.{uF,uV}` is a
proposition definition, not a theorem or an axiom. It states that a
square-integrable irreducible representation gives integrable weighted Whittaker
squares on the actual left-unipotent quotient, for the standard and for the
inverse Whittaker character. The integrability claims remain a proof obligation.

## Statement and existing definitions

The binders and installed instances are those of
`SquareIntegrableEqualRankAnalyticStatement`. The statement quantifies over:

- every prime `p`, every `F : PadicField.{uF} p` and every supplied
  `T : F.TopologicalData`;
- every `n : ℕ`, i.e. every positive rank `n + 1`, so rank one (`n = 0`) is
  included;
- every `ψ : UnitaryAdditiveCharacter F.Carrier`.

The topology, valuation and local-field structure are those of `T`. No equality
with the canonical topological data is assumed. The group
`Langlands.GeneralLinear (n + 1) F.Carrier`, its subgroup
`upperUnipotent (n + 1) F.Carrier` and the actual left quotient
`LeftUnipotentQuotient n F.Carrier` carry their Borel measurable structures.

The statement then quantifies over the following data:

- every `Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)` instance;
- every measure `μ` on the quotient satisfying `QuotientIntegration.IsCompatible`
  with `generalLinearHaar F.Carrier n` and `unipotentHaar F.Carrier n`;
- a complex vector space `V : Type uV`, in a universe independent of `uF`;
- a representation `π` of `GL_(n+1)(F)` on `V`, with the hypotheses
  `Representation.IsIrreducible π` and `T.IsSquareIntegrable π`.

Both Haar measures keep their published normalizations on integral points. No new
measure and no measure-existence assumption is introduced.

The conclusion is a conjunction of two clauses.

1. Standard character. For every `ℓ : glFunctionals ψ n π`, every
   `f : (coefficientModel π ℓ).toSubmodule`, every
   `Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)` and every real `a` with
   `0 < a`, the real function

   ```
   fun q => (whittakerNorm ψ f.val q) ^ 2 * ‖Φ (quotientLastRow n q)‖ ^ 2 *
     (quotientDeterminantAbs (normalizedAbsoluteValue T) n q) ^ (2 * a)
   ```

   is `MeasureTheory.Integrable` for `μ`.
2. Inverse character. The same holds for every `ℓ : glInverseFunctionals ψ n π`
   and every `f : (coefficientModel π ℓ).toSubmodule`, with `inverseWhittakerNorm`
   in place of `whittakerNorm` and the same displayed formula.

The squares `^ 2` are natural-number powers. The determinant power `^ (2 * a)`
is the real power of the positive real number `quotientDeterminantAbs … q`.
Integrability is real Bochner integrability: almost-everywhere strong
measurability together with a finite integral of the absolute value.

The four functions in the integrand are the published norm data of
`WhittakerNormData`, descended to the quotient. On a coset of
`g ∈ GL_(n+1)(F)` they take the values `‖f(g)‖`, `‖Φ(e_(n+1) g)‖` and
`|det g|`, where `e_(n+1) g` is the last row of `g`. Before descent the
integrand is therefore

\[
 |W(g)|^2\,|\Phi(e_{n+1}g)|^2\,|\det g|^{2a},
\]

where `W = f.val` is the coefficient-model function. It is well defined on
`N_(n+1) \ GL_(n+1)` because the norm removes the unitary Whittaker character,
of either sign, and the last row and determinant are invariant under left
upper-unipotent multiplication. The absolute value is the existing
`normalizedAbsoluteValue T`, with value `q⁻¹` on a uniformizer.

Arbitrary complex Schwartz–Bruhat functions are allowed. Only `‖Φ‖²` appears,
so no positivity of `Φ` is required.

### No genericity or nonzero data

Zero functionals, zero model vectors and the zero Schwartz–Bruhat function are
included. If `ℓ = 0`, its coefficient map is zero, the coefficient image contains
only the zero function, and both norm functions vanish identically
(`whittakerNorm_zero`, `inverseWhittakerNorm_zero`). The integrand is then
identically zero, hence integrable. The statement neither assumes nor asserts
the existence of a nonzero Whittaker functional. It assumes no genericity, no
Whittaker norm bound or gauge estimate, no convergence or holomorphy of a JPSS
integral, no alternative square-integrability predicate and no form of the
integrability claim itself.

### Two kinds of square-integrability

The hypothesis `T.IsSquareIntegrable π` is the analytic predicate from
`Classification.Tempered`. For every Borel Haar measure on the actual central
quotient `GL_(n+1)(F) ⧸ Z`, it requires `IsSquareIntegrableModCenter`:
admissibility, a unitary central character, and `MemLp … 2` of the absolute
value of every smooth-dual matrix coefficient on that central quotient.

The conclusion lives on a different space. It concerns Whittaker functions,
not matrix coefficients, on the left-unipotent quotient `N_(n+1) \ GL_(n+1)`.
The conclusion also carries the weights
`|Φ(e_(n+1) g)|²` and `|det g|^(2a)`. Passing from the first kind of
square-integrability to the second is the content of the future proof. In
particular, the source's input (2), square-integrability of the restricted
Whittaker functions modulo `N_r Z_r`, is not a hypothesis here and must be
derived from the matrix-coefficient predicate.

## Why both character signs

In JPSS a pair `(W, W')` uses `W` in the `ψ`-model of one representation and
`W'` in the `ψ⁻¹`-model of another. The equal-rank integrand of
`SquareIntegrableEqualRankAnalyticStatement` pairs `f.val` from
`glFunctionals ψ n π` with `f'.val` from `glInverseFunctionals ψ n σ`. The
intended use applies the standard clause to `π` and the inverse clause to `σ`.

Worker 462's equal-rank draft, the context of this task, uses only this
elementary assembly. Write `Φ₀ = √‖Φ‖` and `a = Re(s)/2`. By the arithmetic and
geometric mean inequality, the norm of the equal-rank integrand is at most the
average of the two weighted squares for `Φ₀`:

\[
 |W W' \Phi|\,|\det|^{\mathrm{Re}\,s}
 \le \tfrac12\big(|W|^2+|W'|^2\big)\,\Phi_0^2\,|\det|^{2a}.
\]

This explains the two signs and the exponent `2 * a`. That assembly is not part
of this module. It also supplies neither estimate.

## Original source and provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105** (1983),
367–464, Section 8.3, printed pages 448–451; registered source
`jpss-1983-rankin-selberg`. The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
In this file, printed pages 448–451 are zero-based PDF indices 82–85 (one-based
pages 83–86). The pages were read visually. No source-specific erratum file was
found in the project literature or in the Library's public notes.

This statement is a derived specialization, not a verbatim result of the source.
The proposition of Section 8.3 (printed p. 448) states absolute convergence of
`Ψ(s, W, W', Φ)` for `Re(s) > 0` when the representations are square-integrable
and `r = t`, together with an unequal-rank assertion. On printed p. 451, in the
case `r > t`, the source bounds the square of an integral by the product of two
integrals. The second factor is

\[
 \int_{N_t\backslash G_t} |W'|^2(g)\,\Phi^2[\eta_t g]\,|\det g|^{2s}\,dg ,
\]

which the source calls finite "by the previous case", i.e. by the equal-rank
argument. This module states exactly that kind of weighted square for a single
representation, with `η_t g` the last row, `s` renamed `a`, and both character
signs. It is not a proof of the equal-rank case, and it does not state the
equal-rank or unequal-rank convergence of `Ψ`.

The source's wording on p. 451 has `s ≥ 0` and `Φ ≥ 0`. This statement requires
`0 < a`, matching the half-plane `Re(s) > 0` of the equal-rank case it
specializes. The endpoint `a = 0` is not asserted. A nonnegative `Φ` is replaced
by `‖Φ‖` for arbitrary complex `Φ`.

### The source route the proof is expected to follow

The equal-rank argument on printed p. 449 has three parts. Adapted to
`|W|² |Φ|² |det|^(2a)`, they read as follows.

- **Central integration formula, p. 449 (1)–(3).** Formula (1) writes an
  integral over `N_r \ G_r` as an integral over
  `(N_(r-1) \ G_(r-1)) × Z_r × K_r` of `F[(g 0; 0 1) z k] |det g|⁻¹`.
  Formula (3) is its application to the equal-rank integrand. For the central
  element `z = t · 1`, the last row of `(g 0; 0 1) z k` is `t η_r k` and its
  determinant has absolute value `|det g| |t|^r`. Since the central character is
  unitary, the integrand factors. One factor is an integral over
  `N_(r-1) \ G_(r-1)` of the restricted Whittaker square times
  `|det g|^(2a-1)`. The other is a Tate-type integral over `t ∈ F^×` of
  `|Φ(t η_r k)|² |t|^(2ra)`, which converges for `a > 0`. The outer integral is
  over the compact group `K_r`.
- **Restricted Whittaker square norms, p. 449 (2).** For `W` in the Whittaker
  model, `∫_(N_(r-1) \ G_(r-1)) |W[(g 0; 0 1)]|² |det g|⁻¹ dg = ‖W‖² < ∞`. The
  source deduces this from `K`-finiteness and square-integrability modulo
  `N_r Z_r`.
- **Determinant split and gauge tail, p. 449 (4)–(5).** The source splits the
  restricted integral into `|det g| ≤ 1` and `|det g| ≥ 1`. On the first part
  the weight `|det g|^(2a-1)` is at most `|det g|⁻¹` because `a > 0`, so (2),
  applied to the right translates of `W` by `K_r`, bounds it. On the second part the Whittaker functions are majorized by gauges
  (2.5), and the resulting integrals (5) converge for large exponents (2.7). Since
  `|det g| ≥ 1`, a larger exponent only increases them.

The source writes this route for the product `|W W'|`; the weighted square is
the case where both factors have the same absolute value. This module neither
assumes nor proves formula (1) on the Library's quotients, the restricted-norm
identity (2), the gauge majorization (2.5) or its integrability (2.7). They
belong to the proof task and are not needed for this statement to be well
formed.

The source works over non-Archimedean local fields. This statement uses the
existing `PadicField` interface, keeps every positive rank including rank one,
and uses every compatible quotient measure and the actual coefficient images.
It adds no convergence, holomorphy, rational-continuation or local-factor
conclusion. General normal convergence and holomorphy are a separate Mellin
task, as are the larger-rank restriction-square and last-row cutoff statements.
