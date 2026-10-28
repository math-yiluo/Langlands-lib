# An actual equal-rank JPSS integral with rational value one

Author: Worker 408.

`Langlands.RankinSelberg.equalRankUnitValue` proves exactly
`Langlands.RankinSelberg.EqualRankUnitValueStatement.{uF,uV,uW} F T n`.
The field universe and the two representation-carrier universes remain
independent. Every supplied `F.TopologicalData`, every natural `n` including
rank one (`n = 0`), every character and compatible quotient measure in the
target, and every specified nonzero functional pair are retained.

## Implemented proof

The proof installs the supplied topology, valuative relation and local-field
structure, followed by exactly the target's Borel structures on the general
linear group, its upper-unipotent subgroup and the left-unipotent quotient.
It then introduces the original target telescope.

The published theorem `Langlands.whittakerTypeKirillov` is applied separately
at universes `{uF,uV}` and `{uF,uW}`. These two proved specializations supply
the arguments of `hasEqualRankCompactTest_of_kirillov`. That published
construction gives `HasEqualRankCompactTest` for the original representations
and functionals and the supplied `normalizedAbsoluteValue T`.

In this construction, compact smooth mirabolic functions for opposite
characters are lifted into the actual coefficient images. The published
`modelKirillovTransfer` transports canonical Kirillov lifting to the supplied
topology using the existing topology equalities. For the second lift,
`standardCharacter_scale_neg_one` reinterprets the inverse character while
preserving the original linear functional and function values. A coefficient
preimage vector then supplies the original inverse-character model.

Smoothness in the two Whittaker-type hypotheses supplies a common compact
open right stabilizer whose determinants have supplied absolute value one.
`lastRowCompactOrbit` supplies the exact Schwartz--Bruhat indicator of its
last-row orbit and the required mirabolic factorization. Together with the
mirabolic product-indicator identity, these give the six existing
`IsEqualRankCompactTest` conditions. The mirabolic compact set contains the
identity and also has determinant absolute value one.

The final application is
`HasEqualRankCompactTest.one_mem_equalRankRationalValues hμ
T.residueCardinality`. Its published proof thickens the compact mirabolic
set by the compact open right stabilizer and projects to the actual
left-unipotent quotient. This set is compact, open and nonempty, so the
given compatibility hypothesis makes its measure positive and finite.
The actual integrand is its indicator for every complex spectral parameter.
Rescaling the first coefficient vector by the inverse of this nonzero
complex volume makes the actual integral one. The vector remains in the
same coefficient image, and the Schwartz--Bruhat function and second vector
are retained. The constant rational function one has denominator one, giving
the required `HasRationalContinuation` witnesses in `equalRankRationalValues`.

Thus the result is literal membership of `(1 : RationalFunctions)` in the
target's existing rational-value set. The specified measure, residue
cardinality and normalized absolute value enter the final application.
The proof covers possibly reducible Whittaker-type representations: smooth
coefficient vectors and compact determinant-unit tests supply the needed
invariance. The imported constructions cover `n = 0` as well.

## Original source and derived provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin--Selberg
Convolutions*, American Journal of Mathematics 105 (1983), 367--464.
Registered source: `jpss-1983-rankin-selberg`. Retained original:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
SHA256:
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.385--386 and 393 (one-based PDF pages 20, 21 and 28) were read
visually during this task, and the registered errata search found no
source-specific correction affecting these passages.

Sections 2.1--2.2, pp.385--386, supply the Whittaker-type scope, coefficient
functions and compact mirabolic inclusion. Page 393, in the equal-rank case
of the proof of Theorem 2.7(i)--(ii), chooses opposite compact mirabolic
functions, lifts them to Whittaker functions, chooses a common right
stabilizer and its last-row test, and normalizes the resulting integral.

This module is a derived application of the three imported Library modules.
The direct quotient-indicator and positive-finite-volume calculation is the
internal assembly implemented in `EqualRankCompactAssembly`,
`EqualRankUnitNormalization` and `QuotientMass`, through `EqualRankCompactTest`.
It supplies the same unit-value conclusion by this route. The supplied-data
transport and independent-universe specialization are internal interface
steps. The target and all its imported Lean/Markdown pairs are unchanged.
