# Existence of symmetric p-adic L-polynomials

Author: Worker 184.

`Langlands.RankinSelberg.symmetricLPolynomialExists.{uF,uV,uW}` proves exactly
[SymmetricLPolynomialExistenceStatement](SymmetricLPolynomialExistenceStatement.md).
The theorem has no additional hypotheses. It retains the canonical p-adic
field data, every nontrivial unitary additive character, the supplied self-dual
Haar measure, independent field and representation universes, and all positive
ranks in either order, including equal rank. Its representations have the full
published Whittaker-type scope, which includes reducible representations.

## Character transport

The private lemma `inverseWhittakerType` transfers the selected second
representation's standard-character Whittaker-type hypothesis to the inverse
standard character. It composes the inverse of
`Whittaker.characterChangeFunctionalEquiv` at the unit `-1` with the given
linear equivalence from standard Whittaker functionals to `ℂ`.
`standardCharacter_scale_neg_one` identifies the resulting functional space
with the inverse-standard space. Admissibility and finite generation are
retained directly. This argument does not impose irreducibility or change the
representation.

## One polynomial for all compatible quotient measures

The private lemma `orderedLPolynomialExists` treats ranks `n ≤ r` with the
canonical topology and Borel structures. It imports the published
[equalRankAnalytic](EqualRankAnalyticProof.md),
[unequalRankAnalytic](UnequalRankAnalyticProof.md), and
[unequalRankCommonGenerator](UnequalRankCommonGeneratorProof.md) theorems.
Each is applied at `F.canonicalTopologicalData` with independent universes
`uF,uV,uW`.

At strict unequal rank the proof applies
`UnequalRankCommonGeneratorStatement.pairLPolynomialExists`, using the actual
common-generator theorem and the unequal analytic theorem for every permitted
block. At equal rank it applies
`EqualRankAnalyticStatement.pairLPolynomialExists` with the actual equal
analytic theorem. In both cases the quotient measure is the fixed canonical
`unipotentQuotientHaar`, and the additive Haar measure is the supplied one.
The helper itself works for any supplied additive Haar measure.

The proof selects the resulting polynomial before introducing any other
quotient measure. `quotientHaarExistence` supplies the right-invariance witness
and compatible-measure existence required by `IsPadicPairLPolynomial`.
For each compatible measure, `unipotentQuotientHaar_unique` identifies it with
the canonical quotient measure at the fixed ambient and subgroup Haar
normalizations. Rewriting that equality transfers the same polynomial and
its full `IsPairLPolynomial` relation. Thus the existential polynomial lies
outside the universal measure quantifiers. Its constant term is one, and its
reciprocal generates the required Laurent spans, including all permitted
unequal-rank blocks.

## Both rank orders and universes

The public proof introduces exactly the closed statement's data and splits
`n ≤ r`. In that branch it applies the ordered helper with universe order
`uF,uV,uW` and representations `(π,σ)`. Otherwise it applies the same helper
with universe order `uF,uW,uV` and representations `(σ,π)`. Unfolding
`IsPadicSymmetricLPolynomial` in the respective branch gives the conclusion.
Equal rank retains the original representation order. The underlying additive
measure is exactly `ν.val` from the supplied self-dual Haar measure throughout.

## Original source and derived provenance

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
at `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Worker 184 verified the hash and visually read printed pages 390–391
(PDF pages 25–26), Theorem 2.7(i)–(ii), and printed page 403 (PDF page 38),
Section 2.12. The former supplies the normalized reciprocal-polynomial
generator and unequal-block independence for representations of Whittaker
type; the latter gives the opposite-rank convention. No JPSS-specific erratum
was found among the project, workspace and literature filenames checked.

This module is a derived assembly from the published analytic results,
conditional pair-L bridges, character equivalence, and quotient Haar existence
and uniqueness. Its private lemmas implement these transports, rather than a
new analytic argument. It uses no factor functional equation or L-factor
multiplicativity premise. The substantive analytic theorems are reused by
import, and no analytic or factor-existence assumptions remain in the public
theorem. Only this new proof pair is submitted.
