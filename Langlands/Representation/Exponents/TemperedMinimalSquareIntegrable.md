# Square-integrability of the quotient chosen at a minimal unitary support

Author: Worker 4772. This is internal supporting work for the necessity part
of Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VII.2.6, Theorem, first proof paragraph (printed p.231 /
PDF p.237). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. No new
source assertion is stated: the module composes Library constructions, and
two of its results keep published propositions as explicit hypotheses.

## Source step

Renard chooses a standard parabolic `P = MN` minimal with `(r_P^G V)_0 ≠ 0`,
takes an irreducible quotient `σ` of `(r_P^G V)_0`, and says that `σ` is
square-integrable modulo the center "by the VII.2.4 lemma and the minimality
of `P`". Frobenius reciprocity then embeds `V` into `i_P^G σ`. The Library
already has the minimal choice among all actual parabolics
(`minimalUnitaryJacquetSupport`), the irreducible quotient
(`unitaryJacquetIrreducibleQuotient`) and the embedding
(`temperedUnitaryJacquetQuotientInductionMap`). This module supplies the
minimality argument and assembles the three.

## Setting

The field `k : Type u` is a Hausdorff nonarchimedean local field and the
carrier universe `v` is independent. `G` is connected reductive; its
rational points carry `RationalPointFamily.pointTopology`, with the supplied
`LocallyCompactSpace` and `NonarchimedeanGroup` instances. A
`UnitaryJacquetSupportData π` records an actual parabolic `p : P ⟶ G`, a
rational Levi `l : M ⟶ P`, a matching geometric unipotent radical, the
multiplication isomorphism, a split component of `M`, and nontriviality of
the actual unitary Jacquet part. Its minimality (`IsMinimal`) is inclusion
minimality of the all-test subgroup functor `SubgroupFunctor.range p` among
all such data. The Levi points carry `leviPointTopology`, with local
compactness and the nonarchimedean structure derived from those of `G(F)`.

## Declarations

`UnitaryJacquetSupportData.IsMinimal.unitaryJacquetPart_quotient_eq_bot`.
Let `π` be normalized-exponent tempered, `D` a minimal support datum and `Q`
any `UnitaryJacquetIrreducibleQuotientData` for `D`, that is, an irreducible
smooth representation `Q.quotient` of `M(F)` with a surjective morphism from
`leviUnitaryJacquetModule`. Then for every actual parabolic `pL : PL ⟶ M`
with `¬ IsIso pL`, every rational Levi `mL : N ⟶ PL`, matching radical and
multiplication isomorphism, and every split component `b` of `N`, the unitary
Jacquet part of `Q.quotient` along these data is `⊥`. No further hypothesis
is used.

`UnitaryJacquetSupportData.IsMinimal.isSquareIntegrableModCenter_quotient`
assumes the exact published `TemperedSquareIntegrableUnitaryPartStatement`
(the VII.2.4 Lemma) at universes `u, v`. Under the same data it concludes
that `Q.quotient` is square-integrable modulo the center of `M(F)` for every
measurable structure, Borel structure and Haar measure on
`M(F) ⧸ Subgroup.center M(F)`.

`IsNormalizedExponentTempered.exists_squareIntegrable_induction_embedding`
assumes `ArbitraryParabolicQuotientCompactStatement` and
`TemperedSquareIntegrableUnitaryPartStatement`. For an irreducible
normalized-exponent tempered `π` it concludes exactly the right-hand side of
`TemperedIrreducibleDiscreteSeriesStatement`. That is: some actual parabolic,
rational Levi, matching radical and multiplication isomorphism, and some
irreducible `σ` of `M(F)`, square-integrable modulo the center for every
Haar measure, admit an injective intertwiner from `π` into
`(leviInductionFunctor p l r hp hr hl hmul).obj σ`.

## Proof of the vanishing theorem

Write `σ₀ = leviUnitaryJacquetModule … π`. The published proof
`unitaryJacquetPartTempered` makes `σ₀` normalized-exponent tempered on
`M(F)`. Temperedness gives admissibility of the actual Jacquet module of
`σ₀` along `pL` (`isAdmissible_jacquetFunctor_obj`). Hence
`unitaryJacquetPart_eq_bot_of_surjective_intertwining`, applied to the
surjection `σ₀ → Q.quotient`, reduces the claim to vanishing of the unitary
part of `σ₀` along `pL`.

Suppose instead that some normalized exponent `χ` of the Jacquet module of
`σ₀` along `pL` has zero normalized real part (`unitaryJacquetPart_eq_bot_iff`).
The published `leviParabolicExtension` gives an actual parabolic `R` of `G`
with Levi exactly `N`, embedding `N → R → G` equal to `N → PL → M → P → G`,
`range pR ≤ range p`, and `range (pL ≫ l ≫ p) = range (l ≫ p) ⊓ range pR`.
Evaluating at the identity test scheme gives the point-level hypotheses of
`isNormalizedJacquetExponent_of_nestedUnitary`. That theorem, built on
normalized transitivity, shows that `χ` is a normalized exponent of the
Jacquet module of `π` along `R`, with the same split component `b`. Its
weight space lies in the unitary part, so the unitary part of `π` along `R`
is nonzero, and these data form a support datum `E`. Minimality of `D`
gives `range pR = range p`. Then
`range (l ≫ p) ≤ range (l ≫ p) ⊓ range p = range (pL ≫ l ≫ p)`, and the
published `IsClosedSubgroup.isIso_of_range_le_range_comp` makes `pL` an
isomorphism, contradicting `¬ IsIso pL`.

## Proof of the two conditional results

For square-integrability, `σ₀` is tempered as above. Quotient closure
(`IsNormalizedExponentTempered.of_surjective_intertwining`) makes
`Q.quotient` tempered. The published admissible-Schur construction
`UnitaryJacquetIrreducibleQuotientData.centralCharacter` gives a full-center
character acting by scalars. The criterion
`TemperedSquareIntegrableUnitaryPartStatement`, applied on `M` with this
character, turns the vanishing theorem into square-integrability for the
given Haar measure. The Levi point topology is the canonical one, so the
criterion applies to `M` with its own instances.

For the embedding, irreducibility makes `π` nontrivial. The minimal datum
`D := minimalUnitaryJacquetSupport hπ` exists by the published noetherian
argument. The compactness hypothesis supplies the compact-quotient instance
for `D.p`. Temperedness supplies the complementary splitting, and
`unitaryJacquetIrreducibleQuotient` chooses `Q`. The output is `Q.quotient`
with its irreducibility, the square-integrability just proved, and the
published injective map `temperedUnitaryJacquetQuotientInductionMap`.

## Scope

The parabolics are arbitrary actual rational parabolics, not standard
ones. Minimality is over all actual parabolic data with any split
component. The field and carrier universes are independent, and all
local-field, topology and connected-reductive hypotheses are retained.
Compactness of actual parabolic quotients and the VII.2.4 Lemma remain
explicit hypotheses of the last two results. Their proofs are separate
tasks, and this module proves neither. It proves no part of the uniqueness
assertion or of the Corollary.
