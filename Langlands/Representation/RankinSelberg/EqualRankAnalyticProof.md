# Equal-rank JPSS convergence, rationality and normalized generator

Author: Worker 64.

`Langlands.RankinSelberg.equalRankAnalytic` proves exactly
`Langlands.RankinSelberg.EqualRankAnalyticStatement.{uF,uV,uW} F T n`
from `Langlands.Representation.RankinSelberg.AnalyticStatement`.
The field and two representation-carrier universes remain independent.
Every prime, p-adic field, supplied `F.TopologicalData`, and positive rank
`n + 1`, including rank one, is retained. The theorem covers admissible
finite-type representations of Whittaker type, including reducible ones,
every specified nonzero functional pair, and every compatible quotient
measure in the target.

The four conclusions concern the existing actual coefficient-model
integrals: absolute convergence on a right half-plane for each pair of
coefficient vectors and Schwartz–Bruhat row test, rational continuation
there, one common nonzero Laurent denominator for all rational values, and
existence of a generator `P(X)⁻¹` with `P(0) = 1` for their Laurent span.
The absolute value is the supplied `normalizedAbsoluteValue T`, and the
spectral variable is `q⁻ˢ` for `q = T.residueCardinality`.

## Implemented proof

The proof installs the topology, valuative relation and local-field
structure supplied by `T` and exactly the target's Borel structures on
the general linear group, upper-unipotent subgroup and left-unipotent
quotient. It then introduces the original target telescope.

Two applications of `modelAsymptoticTransfer` use the proved full-torus
expansion `Langlands.whittakerTypeAsymptotic` at universes `{uF,uV}` and
`{uF,uW}` separately. The first application uses the standard character;
the second uses the inverse standard character. The transport theorem
identifies the supplied topology with the canonical one and transfers
the expansions to the actual coefficient images, using surjectivity of
their model maps. Each finite family is uniform before the functional
and vector are selected. The full-torus theorem includes the central
coordinate through its proved coefficient-image character construction;
it adds no scalar-action hypothesis on the original carrier.

`equalRankQuotientAnalytic` is applied to these expansions, the smoothness
fields of the two Whittaker-type hypotheses, the proved
`finiteFunctionMellin.{uF}`, and `quotientIwasawaIntegration F T n`.
The quotient theorem uses finite-function Mellin analysis in root
coordinates and the quotient Iwasawa formula with its inverse-modulus
weight. It first proves actual quotient integrability on a right
half-plane, then identifies the convergent quotient integral with the
compact-root integral and transfers its rational continuation. Its
single nonzero Laurent denominator clears every rational continuation,
uniformly in the coefficient vectors and Schwartz–Bruhat test.
Specializing its conclusions to the original functionals and supplied
compatible measure gives the first two target clauses. Its denominator
witness packages directly as `HasCommonDenominator` for the existing
`equalRankRationalValues` set.

The proved `equalRankUnitValue.{uF,uV,uW}` supplies literal membership of
one in that same set for the original nonzero functionals and specified
measure. Its compact mirabolic construction lifts opposite-character
tests into the actual coefficient images and normalizes by the positive,
finite mass of a nonempty compact open subset of the actual quotient.
Thus one is the rational continuation of an actual integral.
`mem_zetaSpan` places it in the Laurent span. Finally,
`normalizedGeneratorExistence` applies the common denominator and this
membership: principality gives a rational generator, and removing the
Laurent unit from its inverse gives a reciprocal polynomial normalized
at zero. This proves the fourth clause.

All mathematical inputs are imported proved declarations. The assembly
has no additional expansion, Mellin, Iwasawa, unit-value or generator
premise. It preserves the supplied measure and normalized absolute value
throughout. The target and its imported Lean/Markdown pairs are unchanged.

## Original source and derived provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered source `jpss-1983-rankin-selberg`. Retained original:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original scan's printed pp.390–393 were read visually during this task.
Theorem 2.7(i)–(ii), pp.390–391, gives the convergence, rationality,
fractional ideal and normalized generator. The equal-rank proof uses
Iwasawa integration and root coordinates on p.391, finite-function Mellin
reduction and a denominator independent of the test data on p.392, and
the integral equal to one and normalized generator on p.393.

This module is an internal assembly of the seven imported Library proof
modules. Its topology transport, independent-universe specializations,
quotient integration interfaces and Laurent normalization follow their
implemented proofs. Their paired Markdown explains the underlying
constructions and source correspondence, including the Whittaker
expansion's JPS (1979) provenance. The present module does not repeat
those analytic constructions or assert any unequal-rank or functional
equation conclusion.
