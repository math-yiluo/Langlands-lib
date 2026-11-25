# Getz–Hahn Theorem 11.5.2, p-adic case: unitary generic L-polynomials on `Re(s) ≥ 1`

Module
`Langlands.Representation.RankinSelberg.UnitaryGenericLPolynomialNonvanishingProof`,
namespace `Langlands.RankinSelberg.UnitaryGeneric`. This is the main module of
the proof of the published statement
`Langlands.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement` (module
`Langlands.Representation.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement`).
The proof changes no published file.

## Main theorem

```lean
theorem Langlands.RankinSelberg.UnitaryGeneric.unitaryGenericLPolynomialNonvanishing :
    UnitaryGenericLPolynomialNonvanishingStatement.{uF, uV, uW}
```

This is exactly the target, with its three universes. For every prime `p`, every
`F : PadicField p` (canonical topology), every unitary additive character
`ψ`, every self-dual Haar measure `ν`, all `r, t` and all
representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)` that are generic
for `ψ` (`Whittaker.IsGeneric`: irreducible, admissible, with a nonzero standard
Whittaker functional) and unitarizable (`IsUnitarizable`): every `P : ℂ[X]`
with `IsPadicSymmetricLPolynomial F ψ ν.val π σ P` satisfies
`P.eval (q ^ (-s)) ≠ 0` for every `s` with `1 ≤ Re s`, where `q` is the residue
cardinality. Existence of `P` is neither assumed nor proved.

## Route

The proof follows the route of the statement Markdown ("Intended proof route")
and of the published square-integrable case
`squareIntegrableLPolynomialNonvanishing` (module
`SquareIntegrableLPolynomialNonvanishingProof`), with one addition for
the boundary line `Re(s) = 1`.

1. **Square-summability on `N \ P`** (`UnitaryWhittakerTorusSum`):
   Jacquet–Shalika I, (1.3.1), from the published `padicCellBound`.
2. **Restriction estimate** (`UnitaryWhittakerRestriction`):
   `∫ |W(diag(g, 1_(k+1)))|² |det g|^(-k) dg < ∞`.
3. **Weighted square** (`UnitaryWeightedWhittakerSquare`):
   `∫ |W|² |Φ(e x)|² |det x|^(2a) dx < ∞` for `a ≥ 1/2`, both character signs,
   with the unitary central character from Schur's lemma and the invariant form.
4. **Convergence and holomorphy** (`UnitaryEqualRankAnalytic`,
   `UnitaryZeroRowAnalytic`): the equal-rank integral (11.20) and the zero-row
   integral (11.19, top) converge absolutely on `Re(s) ≥ 1` and are holomorphic on
   `Re(s) > 1` (Getz–Hahn Proposition 11.5.1(a); for equal rank
   Jacquet–Shalika I, Proposition (1.5)(i)). The equal-rank module also proves the
   published `UnitaryEqualRankConvergenceStatement`.
5. **Boundary regularity** (`BoundaryRationalRegularity`): a function holomorphic
   on `Re(s) > 1`, bounded on `1 < Re(s) < 2`, with a rational continuation `R` in
   `q^(-s)`, has `R.denom(q^(-s)) ≠ 0` for all `Re(s) ≥ 1`. The integrals of step 4
   are bounded on the strip because they converge at `s = 1` and `s = 2`
   (`norm_integral_cpow_le_of_strip`).
6. **Assembly** (this module).

## Declarations of this module

- `equalRank_strip_bounded`, `zeroRow_strip_bounded`: an equal-rank (resp.
  zero-row) integral converging at `s = 1` and `s = 2` is bounded on
  `1 ≤ Re(s) ≤ 2`. The integrand is `I_s = c · |det|^(s - κ)` with `κ = 0`
  (resp. `κ = (k+1)/2`), and `norm_integral_cpow_le_of_strip` applies.
- `eval_ne_zero_of_unitary_pair`: for the ordered pair relation
  `IsPadicPairLPolynomial F ψ ν π σ P` (larger rank first) and irreducible
  admissible unitarizable `π`, `σ`, `P(q^(-s)) ≠ 0` for `Re(s) ≥ 1`.
- `eval_ne_zero_of_unitary_symmetric`: the same for
  `IsPadicSymmetricLPolynomial`, by the published
  `isPadicSymmetricLPolynomial_of_le` / `_of_lt`.
- `unitaryGenericLPolynomialNonvanishing`: the target.

## Proof of `eval_ne_zero_of_unitary_pair`

As in the published `IsPadicPairLPolynomial.eval_ne_zero_of_squareIntegrable`.
The existence clause of the relation gives a compatible quotient measure `μ`,
and the universal clause at `μ` gives the normalized-generator relation. The
point `z = q^(-s)` is nonzero (`spectralPoint_ne_zero_of_pos`).

- **Unequal ranks `t < r`.** Write `r = t + (0 + k + 1)`. The common-generator
  relation contains the zero-row block (`isUnequalRankLPolynomial 0 k`). By the
  published `IsNormalizedGenerator.eval_ne_zero_of_regularAt` it suffices that
  every rational continuation `R` of a zero-row value is regular at `z`. Such a
  value comes with coefficient-model vectors for a standard and an inverse
  functional and a rational continuation of the zero-row model integral.
  `unitaryZeroRowAnalytic` gives convergence on `Re ≥ 1` and holomorphy on
  `Re > 1`; `zeroRow_strip_bounded` gives the strip bound;
  `denom_ne_zero_of_bounded_continuation` gives `R.denom(z) ≠ 0`.
- **Equal ranks.** The same with `isPairLPolynomial_self`,
  `unitaryEqualRankAnalytic` and `equalRank_strip_bounded`.
- **`r < t`** is excluded by `not_isPairLPolynomial_of_lt`.

## Modules of the proof

All are in `Langlands/Representation/RankinSelberg/`, namespace
`Langlands.RankinSelberg.UnitaryGeneric`, each with its own Markdown:
`UnitaryWhittakerTorusSum`, `UnitaryWhittakerRestriction`,
`UnitaryWeightedWhittakerSquare`, `UnitaryEqualRankAnalytic`,
`UnitaryZeroRowAnalytic`, `BoundaryRationalRegularity` and this module.

Published Library modules reused, by Lean name:
`UnitaryCellBound.padicCellBound` and `UnitaryCellMasses`;
`SquareIntegrableWhittakerRestrictionReduction`;
`WeightedWhittakerSquareReduction` (with lemmas of
`UnequalRankIwasawaSupportProof`);
`SquareIntegrableEqualRankAnalyticProof`;
`SquareIntegrableZeroRowAnalyticProof`;
`SquareIntegrableLPolynomialNonvanishingProof`; and the published
`recursiveQuotientIntegration`, `QuotientTorusEnvelope`, `mellinHalfPlane`,
`holomorphicRationalContinuation`, `NormalizedGeneratorRegularityProof`,
`admissibleSchur_centralCharacter`. Where a reused lemma was private, the proof
restates it publicly in its own namespace with the same proof.

## Sources

"p." is the printed page and "PDF" the page of the registered file.

- J. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024),
  registered as `getz-hahn-2024-automorphic-representations` (PDF page = printed
  + 11 in Chapter 11): §11.5, (11.19)–(11.20) and Proposition 11.5.1, p.304
  (PDF 315); (11.21) and Theorem 11.5.2, p.305 (PDF 316). Getz–Hahn deduce
  Theorem 11.5.2 from Proposition 11.5.1 in one sentence in the non-Archimedean
  case. The only §11.5 entry of the October
  2026 errata (`getz-hahn-2024-errata-2026-10`) is that `ψ` is defined twice at
  the top of p.304; it does not affect this proof.
- H. Jacquet and J. A. Shalika, *On Euler products and the classification of
  automorphic representations I*, Amer. J. Math. 103 (1981), 499–558, registered
  as `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`
  (printed page = PDF page + 498): Proposition (1.3), pp.505–507 (PDF 7–9), with
  (1.3.1), p.507; (1.5), Proposition (i), p.507 (PDF 9), proof pp.507–508
  (PDF 9–10).
- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
  convolutions*, Amer. J. Math. 105 (1983), 367–464, registered as
  `jpss-1983-rankin-selberg`: §8.3, pp.448–451 (the square-integrable
  convergence argument whose structure the proof follows).

The route through square-summability on `N \ P` is Jacquet–Shalika's for equal
rank. The unequal-rank zero-row block, the strip bound and the boundary
argument are internal to the project.

## What is not asserted

- The Archimedean case of Getz–Hahn Theorem 11.5.2.
- Existence of the L-polynomial `P`.
- Convergence or holomorphy for `Re(s) < 1`, or any statement about blocks other
  than the zero-row block.
- Jacquet–Shalika I, Proposition (1.5)(ii) (`UnitaryEqualRankNonvanishingStatement`).

## Lean checks

A lake build of all seven modules of the proof, inspecting
`unitaryGenericLPolynomialNonvanishing`, gave no errors or warnings. The
theorem is a theorem with universe parameters `uF`, `uV`, `uW` and depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
