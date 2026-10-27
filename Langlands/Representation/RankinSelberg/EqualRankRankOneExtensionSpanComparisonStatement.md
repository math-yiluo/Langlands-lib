# Equal-rank rank-one extension Laurent-span comparison

This module defines only the proposition
`Langlands.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement`
(universes `uF uV uW`). It proves nothing.

## Meaning of the Lean statement

Fix a prime `p`, a field `F : PadicField.{uF} p` with its canonical
topological data, a unitary additive character `ψ`, an additive Haar measure
`ν` on `F` (for the Borel σ-algebra), and `t : ℕ`. Let `π` be a complex
representation of `GL_(t+2)(F)` on `V : Type uV` and `σ₁` a complex
representation of `GL_(t+1)(F)` on `W : Type uW`, and let `χ` be a
quasicharacter of `F^×`. Assume

1. `π` is of Whittaker type for the standard character `standardCharacter ψ (t + 1)`;
2. `σ₁` is of Whittaker type for `standardCharacter ψ t`.

Let `χlift` be the representation of `GL_1(F)` on `ULift.{uW} ℂ` obtained from
`rankOneCharacter χ` by conjugating with `ULift.moduleEquiv`; only this
rank-one carrier is lifted. Let `I` be the Library's upper normalized
induction `F.canonicalNormalizedProductInduced (twoBlocks 1 (t + 1) …)
(pairFamily χlift σ₁)`, a representation of `GL_(1+(t+1))(F)` in the ordered
blocks `(χ, σ₁)`. This is exactly the induced representation of the endpoint
`Langlands.RankinSelberg.EqualRankRankOneExtensionLDivisibilityStatement`.

With the canonical topology, valuation and local-field structure, the Borel
σ-algebras on `F`, `GL_(t+1)`, `GL_((1+t)+1)`, their upper unipotent subgroups
and the quotients `LeftUnipotentQuotient t` (`N_(t+1) \ GL_(t+1)`) and
`LeftUnipotentQuotient (1 + t)` (`N_(t+2) \ GL_(t+2)`): for all
right-invariance instances of `unipotentHaar F.Carrier t` and
`unipotentHaar F.Carrier (1 + t)`, every measure `μbase` on
`LeftUnipotentQuotient t` that `IsCompatible` with `generalLinearHaar F.Carrier t`
and `unipotentHaar F.Carrier t`, every measure `μind` on
`LeftUnipotentQuotient (1 + t)` that `IsCompatible` with
`generalLinearHaar F.Carrier (1 + t)` and `unipotentHaar F.Carrier (1 + t)`, and
every proof `hrn : t + 1 = 1 + t`, the Laurent span (`zetaSpan`, the
`LaurentCoefficients`-span in `RationalFunctions`) of

- `unequalRankZetaValuesAt (r := t + 1) (n := t) 0 0 rfl q ψ abv μbase
  (rectangularMeasure ν 0 (t + 1)) π σ₁`, the block `j = k = 0` zeta values
  of `π × σ₁`,

is contained in the Laurent span of

- `equalRankZetaValues (n := 1 + t) q ψ abv μind (hrn ▸ π) I`, the equal-rank
  zeta values of `π`, viewed on `GL_((1+t)+1)` by the cast along `hrn`,
  against `I`.

Here `q` is `F.canonicalTopologicalData.residueCardinality` and `abv` is
`normalizedAbsoluteValue F.canonicalTopologicalData`.

Unfolding the Library definitions (`LocalFactor.lean`): a rational function
`R` is a base zeta value when there are `W ∈ whittakerSet ψ (t + 1) π` and
`W₁ ∈ inverseWhittakerSet ψ t σ₁` whose block integral, with `j = 0` and the
rectangular measure on the empty matrix variable, converges absolutely on a
right half-plane and has rational continuation `R(q^(-s))` there. It is an
induced zeta value when there are `W ∈ whittakerSet ψ (1 + t) (hrn ▸ π)`,
`W' ∈ inverseWhittakerSet ψ (1 + t) I` and a Schwartz–Bruhat function `Φ` on
`F^(t+2)` whose equal-rank integral converges absolutely on a right half-plane
and has rational continuation `R(q^(-s))`.

The statement assumes no Whittaker type for `I`, no existence of
L-polynomials and no irreducibility. The cast `hrn ▸ π` is the same cast
that `IsPairLPolynomial` applies in its equal-rank branch when the ranks are
`r = t + 1` and `n = 1 + t`.

## Relation to the endpoint

Given L-polynomials `Pbase` for `(π, σ₁)` and `Pind` for `(π, I)` in the sense
of `IsPadicSymmetricLPolynomial`, `Pbase` is the normalized generator of the
base span above, and `Pind` of the induced span, for any compatible quotient
measures. By the conjunct `NormalizedGeneratorSpanDivisibilityStatement` of
the Library theorem `laurentPolynomialDivisibility`, inclusion of spans
then gives `Pbase ∣ Pind`. The author compiled this reduction privately as a
check; it is not part of this module.

## Source and derivation

This is an internal statement, derived from Jacquet, Piatetski-Shapiro and
Shalika, *Rankin–Selberg Convolutions* (1983):

- Proposition 9.1 (section 9.1, printed pages 452–454, PDF pages 87–89),
  available in the Library as
  `Langlands.Whittaker.TwoBlockWhittakerExtensionStatement`, extends a
  Whittaker function of the second block to a Whittaker function of the
  upper induced representation with prescribed restriction to
  `diag(g, 1)`, up to a Schwartz–Bruhat factor in the last row of `g`;
- printed page 449 (PDF page 84), displays (1) and (3), the last-row
  reduction of an equal-rank integral, stated in the Library as
  `Langlands.RankinSelberg.EqualRankLastRowReductionStatement`.

Combining them shows that each base value `R` has a positive multiple
`c · R` that is an induced value, which gives the span inclusion. The source
does not state this inclusion: it treats the strict-rank case in Lemma (5.5)
and the descent in section 7.2. The equal-rank form here, with the test and
induced ranks both `t + 2`, is the case that the descent needs. Provenance:
derived.

## Intended proof route (not part of the statement)

For a base value `R`, given by `W` and `W₁`:

1. take the 0/1 last-row cutoff `Φ₀` for `W` from
   `ZeroRowLastRowCutoffStatement` (rank `t`, `k = 0`);
2. apply Proposition 9.1 with `a = 0`, `b = t`, the character `ψ⁻¹`, the
   rank-one block `χ` and the block `σ₁`, to `W₁` and `Φ₀`. This gives
   `W'` in the inverse Whittaker set of the induced representation with
   `W'(diag(h, 1)) = W₁(h) Φ₀(e_(t+1) h) |det h|^(1/2)`; transport `W'` to `I`
   along the blockwise `ULift` equivalences;
3. choose a compact open subgroup `J` fixing `W` and `W'` on the right, and
   let `Φ` be the indicator of the last-row orbit of `J`;
4. by the last-row reduction, the equal-rank integral of `(W, W', Φ)` is
   `c` times the corank-one integral of `(W, W₁)`, with the same convergence,
   so `c · R` is an induced value.
