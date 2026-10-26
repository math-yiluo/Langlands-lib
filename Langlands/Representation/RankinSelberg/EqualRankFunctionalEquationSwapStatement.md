# Fixed-character equal-rank epsilon and gamma exchange

Author: Worker 639. The quantifiers and conclusion are extracted from Worker
88's published `EqualRankFactorSwapStatement`; the direct transport plan below
follows the task context supplied by Worker 458.

The module defines the closed proposition
`Langlands.RankinSelberg.EqualRankFunctionalEquationSwapStatement.{uF, uV, uW}`.
It retains exactly the epsilon and gamma conjuncts of
`Langlands.RankinSelberg.EqualRankFactorSwapStatement`, with every outer
quantifier, typeclass parameter and hypothesis in the same order. It imports
that published module and changes none of its definitions. This statement
unit contains no proof or axiom.

## Exact proposition

For every prime `p`, every `F : PadicField.{uF} p` with its canonical
topological data, every `ψ : UnitaryAdditiveCharacter F.Carrier`, every
supplied `ν : LocalFactor.PadicAbelian.SelfDualHaar
F.canonicalTopologicalData ψ`, and every `n : ℕ`, consider actual complex
representations `π` and `σ` of `GL_(n+1)(F)` on `V : Type uV` and
`W : Type uW`. The three universes are independent, and the rank includes
every positive integer, including one.

The character structure includes continuity, unitarity and nontriviality.
The supplied measure is self-dual for this character; this quantifier does
not assert the existence of such a measure. Both representations satisfy
`IsOfWhittakerType n (standardCharacter ψ n)` in the canonical topology.
This is the existing conjunction of admissibility, including smoothness,
finite generation over the group algebra, and a one-dimensional space of
Whittaker functionals. There is no irreducibility hypothesis.

The conclusion is precisely the conjunction:

- For every `e : ℂˣ × ℤ`,
  `IsPadicPairEpsilonFactor F ψ ν.val π σ e ↔
  IsPadicPairEpsilonFactor F ψ ν.val σ π e`.
- For every `G : RationalFunctions`,
  `IsPadicPairGammaFactor F ψ ν.val π σ G ↔
  IsPadicPairGammaFactor F ψ ν.val σ π G`.

Both sides use the original character `ψ` and the same additive Haar measure
`ν.val`. For the residue cardinality `q` of the canonical data, `e = (c, m)`
represents the epsilon monomial `c q^(-ms)`, and `G` represents
`G(q^(-s))`. Exchange preserves the coefficient and exponent of `e` and the
entire rational function `G`.

No factor relation is redefined. In particular, the imported relations
still require existence of a compatible quotient measure and nonzero
standard and inverse-character Whittaker functionals for the first and
second representations. Their equations hold for every compatible quotient
measure and every such pair of nonzero functionals. The equations retain
every coefficient-model vector and Schwartz–Bruhat test, the plus-sign row
Fourier pair `IsRowFourierPair ψ ν.val Φ Φhat`, the rational-continuation
witnesses, and the second model's scalar at minus one. At rank `n + 1` the
functional-equation sign is the `n`th power of that scalar, expressed by
`HasModelMinusOneScalar`. Epsilon certificates also retain their original
and dual normalized generators; gamma certificates retain a nonzero
rational-value witness.

The dual integral uses the actual inverse-transpose pullbacks on the
original representation carriers and the corresponding dual model
functions. These are not identified with smooth contragredients of
possibly reducible representations. The proposition adds no analytic
premise or factor-existence hypothesis and asserts no existence of an
epsilon or gamma factor. Its conclusion has no L-polynomial conjunct.

## Original source and derived content

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
PDF page numbers here are one-based and include the cover.

Section 2.1, printed pages 385–386 (PDF 20–21), defines representations of
Whittaker type, allows replacement of the character by its inverse and
defines the inverse-transpose representation. Its identification with a
contragredient is asserted there under irreducibility. The Lean statement
specializes the source's non-Archimedean local fields to the existing
canonical p-adic interfaces.

Theorem 2.7, printed pages 390–391 (PDF 25–26), supplies the functional
equations and the second representation's minus-one sign. Section 2.12,
printed page 403 (PDF 38), explicitly asserts equal-rank epsilon symmetry
at the same additive character. Its convention of placing the larger rank
first concerns unequal ranks and does not establish the present
equal-rank equivalences merely by definition.

Gamma symmetry is derived content: Section 2.12 does not explicitly state
it. Section 3.1(2), printed page 404 (PDF 39), defines gamma as epsilon
times the dual L-factor at `1-s`, divided by the original L-factor at `s`.
The source's equal-rank epsilon and L symmetries therefore motivate gamma
symmetry for the actual inverse-transpose dual pair as well. The
certificate equivalences here express these equalities using the
Library's existing relations. No matching erratum for this registered
source was present in the checked project and Library errata locations.

## Intended direct derivation

The direct route transports coefficient models and their functional
equations at the fixed character. Use
`a = characterChangeElement (-1) n`, the diagonal matrix with entries
`(-1)^n, …, 1`, to exchange the standard and inverse-character models
before interchanging their coefficient functions. Its bottom row is fixed;
its determinant absolute value and quotient-measure modulus are one.
This should preserve the original integrals and their rational families
with the same Schwartz–Bruhat test.

The required dual-integral calculation also tracks the long Weyl element.
Commuting it past `a` introduces the central matrix `(-I)^n`. The
minus-one scalars of both coefficient models are involutive, so the
resulting product of their `n`th powers converts the original second
model's sign into the exchanged second model's sign. The same original
plus-sign Fourier pair and supplied Haar measure can then be used on both
sides. A proof must establish the matrix identities, model and nonzero
functional transports, compatible-measure transport, rational
continuations, normalized-generator transport and sign calculation, and
apply the construction in both directions. This paragraph specifies the
intended derivation; it supplies no proof of those claims in this module.

A ratio-based derivation instead needs original and actual dual
L-polynomial exchange, matching normalized generators, the original and
dual analytic conclusions needed by the epsilon-to-gamma bridge, and
enough existence and uniqueness to identify every certificate appearing
in the gamma equivalence. In particular,
`IsEqualRankEpsilonFactor.gammaFactor` is conditional on its original and
dual inputs; its availability alone does not discharge those obligations.
Neither route licenses adding any of these premises to this statement.
