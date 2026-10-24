# The JPSS unequal-rank rational functional equation at block zero

Author: Worker 113.

This module defines the fixed-data predicate
`Langlands.RankinSelberg.UnequalRankBlockZeroGammaEquation` and the proposition
`Langlands.RankinSelberg.UnequalRankBlockZeroGammaExistenceStatement.{uF,uV,uW}
F T n r`. The latter is an internal prerequisite extracted from the full JPSS
Theorem 2.7, not a separately named theorem of the source. It states existence
of a nonzero rational functional-equation factor at block zero. It does not
prove existence or perform epsilon normalization.

## Source and scope

The original is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained file is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Relevant printed pages were read visually:

- Theorem 2.7, pp. 390–391: rationality, normalized generators and the
  functional equation for representations of Whittaker type.
- The end of the analytic argument and Section 2.8, pp. 394–395: nonzero
  unequal-rank integral families and reduction to block zero.
- Section 2.11, pp. 398–403: the block-zero bilinear forms, uniqueness argument
  and functional-equation existence.
- The start of Section 2.9, p. 395: the subsequent logical step of showing
  that the normalized epsilon factor, if it exists, is a monomial.

Theorem 2.7 has the full Whittaker-type scope. In contrast, the uniqueness
proposition on p. 399 explicitly assumes that both representations are
irreducible and generic. The target here retains Whittaker type, including
reducible representations. Extending the Section 2.11 argument to that full
scope, or supplying an alternative proof in that scope, is a future proof
obligation. The p. 399 proposition alone is not a proof of this target.
No irreducibility or bilinear uniqueness assumption has been added to Lean.

The rational equation is logically prior to epsilon normalization, although
Section 2.9 occurs earlier in the paper than Section 2.11. From the full
theorem, its factor is
`G(q^(-s)) = epsilon(s) L(1-s, dual pair) / L(s, original pair)`.
Both reciprocal-polynomial generators and the epsilon monomial are nonzero,
so this is a nonzero rational function of `q^(-s)`. The original integral
family is nonzero by the analytic part. This explains the derived target's
provenance; no derivation from the full theorem is implemented or assumed here.
Propagation to all blocks and normalized epsilon assembly remain separate work.

## Fixed data and the actual integrals

The fixed predicate takes the same arguments, in the same order, as
`UnequalRankGammaEquation`: `hnr`, `q`, `psi`, `abv`, `mu`, `nu`, `pi`,
`sigma`, `ell`, `ellPrime`, `G`. Its ambient field and measurable structures
also match that predicate. It fixes `j = 0`, `k = r - n - 1`, and proves the
arithmetic identity `r = n + (0 + k + 1)` from `hnr : n < r`.
The ranks of the actual representations are `r + 1` and `n + 1`;
these are the printed ranks `r` and `t` in JPSS.

The body is precisely the block-zero specialization of the clauses of
`UnequalRankGammaEquation`:

1. There exists `zeta : Complex units` with
   `HasModelMinusOneScalar sigma ellPrime zeta`. Thus minus the identity acts
   by this scalar on the second coefficient model. This is a conclusion;
   a central character on the original carrier is not an assumption.
2. Some `R` in the actual `unequalRankValuesAt 0 k hr ...` is nonzero.
   Its rectangular measure is `rectangularMeasure nu 0 (n + 1)`.
   This clause prevents a vacuous functional equation on an entirely zero
   integral family.
3. For every `f` and `fPrime` in the two actual coefficient models there exist
   rational functions `R` and `Rdual`. They satisfy `HasRationalContinuation`
   for the original `unequalRankIntegralAt 0 k hr ...` and the actual
   `dualUnequalRankModelIntegralAt hnr 0 k hr ...`, respectively, and satisfy
   `GammaFunctionalEquation q zeta r G R Rdual`.

The dual wrapper is the existing definition from `FunctionalEquationStatement`.
It uses the complementary block `k`, the inverse additive character
`psi.scale (-1)`, `firstDualFunction` and `secondDualFunction`, and right
translation of the first transformed function by `blockWeylAt n r hnr`.
The latter is the matrix `diag(I_(n+1), w_(r-n))`. The function transform is
`f(g) -> f(w * inverseTranspose(g))`. The same supplied `nu` gives the dual
measure `rectangularMeasure nu k (n + 1)`; the quotient measure and absolute
value are also unchanged. These are the existing concrete integrals, with no
abstract comparison family substituted for them.

Writing `x(s) = spectralPoint q s = q^(-s)`, the equation is

`Rdual(x(1-s)) = zeta^r * (G(x(s)) * R(x(s)))`.

It holds for each complex `s` at which the denominators of `R` at `x(s)`,
`Rdual` at `x(1-s)`, and `G` at `x(s)` are all nonzero. The sign exponent `r`
is the larger rank minus one. The reflected evaluation is on the dual side.
The fixed predicate does not separately assert `G != 0`; the universal
existence proposition supplies it.

## Universal quantifiers

The universal proposition uses exactly the scope of
`UnequalRankFunctionalEquationStatement F T n r`:

- Every prime `p`, every `F : PadicField.{uF} p` and supplied
  `T : F.TopologicalData`, with the topology and valuation of `T`, actual
  residue cardinality `T.residueCardinality` and `normalizedAbsoluteValue T`.
  As in that existing statement, `p` and its primality instance are implicit
  parameters, and `F`, `T`, `n`, `r` are explicit.
- Every `hnr : n < r`, unitary additive character `psi`, right-invariant
  unipotent Haar instance, compatible quotient measure `mu`, and supplied
  scalar additive Haar measure `nu` satisfying `IsSelfDual psi nu`.
- Independent carriers `V : Type uV`, `W : Type uW` with their complex module
  structures, representations `pi` of `GL_(r+1)` and `sigma` of `GL_(n+1)`,
  and Whittaker-type hypotheses for `standardCharacter psi r` and
  `inverseStandardCharacter psi n`, respectively.
- Every specified pair of Whittaker functionals `ell`, `ellPrime` with
  nonzero underlying linear maps.

Only after these data and hypotheses, it asserts
`exists G, G != 0 and UnequalRankBlockZeroGammaEquation ... G`.
Thus one `G` and the scalar `zeta` inside its equation precede every pair of
coefficient vectors. The continuations may depend on the vector pair.
The statement does not assert independence of `G` from the previously chosen
measures or functionals. Rational continuation, a nonzero original value,
the model scalar and the gamma equation are conclusions, not assumptions.

The Borel structures and additive uniform structure are the same as those
installed by `UnequalRankFunctionalEquationStatement`. The private lemma
`blockZero_valuative_nonarchimedean` repeats that module's bridge from the
valuative open-submodule basis to `NonarchimedeanAddGroup`, needed to formulate
`IsSelfDual`; it adds no hypothesis. All existing Lean/Markdown pairs are
preserved. The two new public declarations are Prop-valued definitions and
assert no axioms or proved existence theorem.
