# Orbit decomposition of σ-discrete series

`Langlands.BaseChange.sigmaDiscreteSeriesOrbitDecomposition` proves
`Langlands.BaseChange.SigmaDiscreteSeriesOrbitDecompositionStatement.{u,v,uW}`.
For a σ-discrete representation of positive rank, it produces an irreducible
square-integrable block in the original carrier universe. The normalized
product along its σ-orbit is equivalent to the original representation after
the specified matrix reindexing. The period condition applies to every
nonnegative exponent.
[Statement and conventions](SigmaDiscreteSeriesOrbitDecompositionStatement.md)

## The invariant multiset of blocks

The characteristic-zero p-adic realization keeps the upper field carrier,
topology and valuation. The proof lifts the input representation to the
carrier universe of `Classification.temperedBlockExhaustion`, which presents
it as a normalized product with irreducible square-integrable unitarizable
blocks. Each occurrence contributes its rank and smooth isomorphism class.
`Classification.temperedBlockUniqueness` identifies equivalence of normalized
products with equality of these multisets. The reverse implication uses a
bijection of occurrences that matches ranks and block isomorphisms, including
when a class has multiplicity greater than one.
[Field realization](../LocalField/CharZeroPadicRealization.md),
[tempered exhaustion](../Representation/Classification/TemperedBlockExhaustionProof.md),
[block uniqueness](../Representation/Classification/TemperedBlockUniquenessProof.md),
[occurrence matching](../Combinatorics/FiniteOccurrenceMatching.md)

Continuous entrywise pullback preserves irreducibility, square-integrability
and unitarizability. It commutes with normalized induction and acts on the
tagged isomorphism classes by keeping their ranks. The σ-intertwiner for the
input representation then makes its block multiset invariant under pullback.
[Analytic transport](../Representation/Classification/InverseTransposeAnalyticProof.md),
[normalized product transport](TwistedCharacter/StableLanglandsData.md)

## Removing one orbit

Choose one block class and take its minimal period `t` under pullback. The
cyclic relation `σ ^ l = 1` supplies a positive fixing exponent. The first
`t` iterates belong to the invariant multiset and are distinct by minimality.
They form an invariant submultiset with one occurrence of each orbit class.
Cancellation in the additive multiset identity shows that the complementary
multiset is invariant as well. This also applies when the complement contains
other copies of the chosen orbit. Composition of entrywise pullbacks
identifies every iterate with the corresponding power of `σ`, so Mathlib's
minimal-period divisibility lemma gives the full stabilizer condition.
[Entrywise composition](SigmaOrbitConjugates.md)

If the complement is nonempty, both submultisets are realized by choosing
original blocks for their occurrences. Their ranks sum to the original rank
and each part has positive rank. Tempered uniqueness compares the original
product with the product of the concatenated blocks. Normalized induction in
stages identifies the latter with the product of two inner inductions. The
invariance of each part and tempered uniqueness make each inner induction
σ-stable.
[Ordered induction in stages](../Representation/Parabolic/FlattenedProductInduction.md)

The tensor product of the two inner inductions gives a smooth σ-stable Levi
action. Twisting it by the positive half-modulus preserves both properties
and makes its unnormalized induction the normalized outer product. The
irreducibility of this induction implies irreducibility of the twisted Levi
action. The standard Levi is a finite product of second-countable general
linear groups, so the separable-group small realization theorem places its
twisted action in the original carrier universe. Transport of the intertwiner
and of smooth induction gives the proper induction excluded by
`IsSigmaDiscreteSeries`. Thus the complement is empty.
[Modulus invariance](SigmaInducedIntertwiner.md),
[inducing action recovery](../Representation/Induction/BlockInducingRecovery.md),
[small realizations](../Representation/Smooth/SmallRealizationProof.md)

## The block and the induced equivalence

The surviving orbit has constant block rank `m`. Summing the ranks in the
multiset equality gives `t * m = n`. Unordered uniqueness compares the
original block product with the uniform shape ordered by
`1, σ, …, σ^(t−1)`. The two field packages give the same normalization on
this shape via the common Levi half-character. The proof composes with
`GeneralLinear.reindex (finCongr h)` in the inverse direction specified by
the statement. The general linear small realization theorem gives a witness
in `Type uW`, and its actual intertwining equivalence transports
square-integrability, the period test and each factor of `sigmaOrbitProduct`.
[Orbit product](CuspidalSigmaLift.md),
[general linear small realizations](../AllField/Representation/Smooth/SmallRealizationProof.md)

## Sources

The implemented argument follows the forward direction of Arthur–Clozel,
Chapter 1, §2.3, Lemma 2.8. The multiset split makes explicit the use of
transitivity and minimality in that argument. Henniart–Lemaire II.4.6 gives
the classification with the stabilizer formulated in terms of the cyclic
group.

- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula* (1989), Chapter 1, §2.3, Lemma 2.8, printed
  p. 17 (PDF p. 31). Literature ID `arthur-clozel-1989-base-change`.
  SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  [Book](https://www.claymath.org/library/cw/arthur/pdf/30.pdf)
- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour
  GL_n en caractéristique non nulle* (2011), II.4.6, printed p. 88 (PDF p. 96).
  Literature ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
  SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
  [Memoir](https://smf.emath.fr/system/files/2017-08/smf_mem-ns_124.pdf#page=96)
