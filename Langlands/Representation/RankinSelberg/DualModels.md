# Dual coefficient models and the intrinsic generator comparison

## Meaning and scope

`Langlands.Representation.RankinSelberg.DualModels` constructs the actual
coefficient-model equivalences underlying the transformed JPSS integrals. It
then proves equality of the transformed rational-value families with the
per-functional rational-value families of the inverse-transpose representations.
The unequal-rank equality exchanges the two rectangular block sizes and includes
the prescribed right translation by the block Weyl representative.

The algebraic equivalences and rational-family equalities require no
multiplicity-one, nonzero-functional, convergence, or generator-existence
hypothesis. The comparison with the **intrinsic** zeta sets requires both dual
representations to be of Whittaker type, both specified original functionals to
be nonzero, and half-plane convergence for every integral in the dual coefficient
models. The L-polynomial comparison is packaged using the corresponding dual
analytic conclusion. These assumptions remain explicit; this module does not
prove the JPSS analytic theorem, preservation of Whittaker type by inverse
transpose, the universal gamma relation, or a contragredient identification.

## Original source and provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, American Journal of Mathematics **105** (1983), 367–464,
registered as `jpss-1983-rankin-selberg`. The retained original PDF has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The cited passages are Section 2.1, formulas (3)–(4), printed p.386, and
Theorem 2.7(ii)–(iii), printed p.391.

Page 386 describes the coefficient image, its invariance under right translation,
and the dual function

\[
  \widetilde W(g)=W(w_{n+1}\,{}^t g^{-1}).
\]

The image belongs to the inverse-transpose pullback with inverse additive
character. The source separately identifies this pullback with a contragredient
under additional hypotheses; that identification is not used here. Page 391
gives the reciprocal-polynomial L convention and the dual integrals in the
functional equations. In unequal rank the dual block is the complementary
block, and its first function is right translated by the block Weyl element.

This is a derived implementation of these model transformations, combined with
the published `AnalyticBridge` comparison. The source does not give the Lean
names, subtype transports, or these exact set-equality formulations. Their
provenance is the coefficient identity and the fact that bijections of the test
models leave the family of integrals unchanged. The original pages were visually
checked against the conventions and formulas below; no project errata note for
this source was found.

## Parameters and normalization

The field `F`, first carrier `V`, and second carrier `W` occupy independent
universes. Representations and functionals have coefficients in `ℂ`. The field
has a topology and `IsTopologicalRing F`; the value-set comparisons require a
measurable structure on the left unipotent quotient. Unequal-rank comparisons
also use a measurable structure on `F` and the existing product rectangular
measure of an `AdditiveHaarMeasure F`.

No local-field hypothesis, residue-cardinality identification, positivity
condition on `q : ℕ`, self-duality, or quotient-measure compatibility is needed
for these algebraic transports. The same given quotient measure and absolute
value occur on each side of every equality. In unequal rank the exchanged block
uses the same additive Haar measure through `rectangularMeasure ν k (n+1)`.
Rank one is included by `n = 0` in equal rank. In unequal rank the smaller group
is `GL_(n+1)`, the larger group is `GL_(r+1)`, and
`r = n + (j+k+1)` with arbitrary natural `j,k`, including zero.

## Constructed maps

`firstDualFunctional ψ π ℓ` is the published Weyl-translated `dualFunctional`,
with its character transported along
`standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n`.
`secondDualFunctional` applies the same construction to the original
inverse-character functional after the corresponding character transport.
The `*_ne_zero` lemmas inherit nonvanishing from `dualFunctional_nonzero`.

The coefficient lemmas assert, for the **same** vector `v`, that the transformed
coefficient is the coefficient of the inverse-transpose representation with
these constructed functionals. `firstDualModelMap` and `secondDualModelMap`
therefore map between the actual coefficient images. Injectivity follows from
injectivity of the underlying dual transform; surjectivity takes a vector
representing the target coefficient and uses that same vector in the source.
`firstDualModelEquiv` and `secondDualModelEquiv` package these bijective linear
maps. These are linear equivalences; this module asserts no additional
intertwining identity for them.

`translateModelEquiv ψ π ℓ a` uses the existing model representation action by
`a`, with inverse action by `a⁻¹`. Its value is exactly `g ↦ f(g*a)`.
`translatedFirstDualModelEquiv` composes the first dual equivalence with this
translation in the target model. Its value formula is exactly
`translateWhittaker (ψ.scale (-1)) n (firstDualFunction ψ n f.val) a`.

## Rational-value sets and intrinsic generators

`dualEqualRankRationalValues_eq` transports both coefficient-model arguments
through the constructed equivalences. The forward and reverse inclusions use
the same Schwartz–Bruhat function and the same rational continuation. The
integrands coincide by the value formulas. The dual family already ranges over
all Schwartz–Bruhat tests; no Fourier surjectivity assertion is needed.

`unequalRankValuesAt_eq_set` unfolds the fixed-rank wrapper by eliminating the
rank equality. `dualUnequalRankRationalValuesAt_eq` then transports the first
model through `translatedFirstDualModelEquiv` at `blockWeylAt n r hnr` and the
second through `secondDualModelMap`. The resulting family is precisely
`unequalRankValuesAt k j` for the inverse-transpose pair and inverse additive
character. This is equality of whole rational-value sets, with the rectangular
block exchanged. It does not identify integrals for different blocks of the
same original pair.

`dualEqualRankZetaValues_eq_rationalValues` and
`dualUnequalRankZetaValues_eq_rationalValues` apply the published intrinsic
comparison after these set equalities. The dual Whittaker-type hypotheses give
multiplicity one; nonzero original functionals give nonzero constructed dual
functionals; the stated half-plane convergence removes the extra convergence
filter in the intrinsic sets. In the unequal-rank theorem the representation
rank is written `n + (k+j+1)` so that the intrinsic set for the **dual** block
`k,j` has its native type. Proofs of the equal natural-number dimensions supply
the `j,k` wrapper on the transformed side.

Finally, `dualEqualRank_isLPolynomial_iff` and
`dualUnequalRank_isLPolynomial_iff` identify the intrinsic dual L-polynomial
predicate with the normalized-generator predicate for the transformed
functional-equation family, assuming the relevant dual analytic conclusion and
the same Whittaker-type and nonvanishing hypotheses. They reuse
`EqualRankAnalyticConclusion.isEqualRankLPolynomial_iff` and its unequal-rank
analogue. No new polynomial is chosen, and no block independence, comparison of
different quotient measures, or analytic existence is inferred.
