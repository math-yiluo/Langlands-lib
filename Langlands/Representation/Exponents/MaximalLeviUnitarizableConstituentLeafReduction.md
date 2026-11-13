# The unitarizable-constituent step of Renard VII.1.3 from two open inputs

Author: Worker 58. Module
`Langlands.Representation.Exponents.MaximalLeviUnitarizableConstituentLeafReduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. This module is an internal
conditional reduction. It proves no new mathematics from the literature. It puts together
published Library theorems and published reductions. It does not prove the target
unconditionally.

## Statement

`MaximalLeviSupercuspidalUnitarizableConstituentLeafReductionStatement.{u, v}` is the
implication

```lean
BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
  CuspidalSupport.RationalNormKernelFixedLevelFinitenessStatement.{u, max u v} →
    MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v}
```

`maximalLeviSupercuspidalUnitarizableConstituent_of_jointBasis_fixedLevel` proves it. The two
premises and the conclusion are published statements, used unchanged.

- `JointSpecialCompactBasisExistenceStatement.{u}` (module
  `Langlands.BruhatTits.SpecialCompact.JointBasisStatement`; Renard V.5.1–V.5.2): for every
  nonarchimedean local field `F : Type u`, connected reductive `G`, maximal split torus and
  generic cocharacter, there are one apartment datum and one special point. At these, the
  special compact subgroup `K0` has the special compact properties, standard-Levi
  inheritance, the ambient and Levi Iwasawa products, the ambient and Levi Cartan
  comparisons and the simultaneous basis property. Task 4169 owns its proof.
- `RationalNormKernelFixedLevelFinitenessStatement.{u, max u v}` (module
  `Langlands.Representation.CuspidalSupport.RationalNormKernelDecompositionStatement`):
  condition (KF) from the proof of Renard VI.3.4. For every compact open subgroup `K` of the
  common norm kernel of `G(F)`, only finitely many isomorphism classes of irreducible smooth
  representations with compact coefficients have a nonzero `K`-fixed vector. Here it is used
  at representation-carrier universe `max u v`. That is the universe of the induced
  representation `i_P ρ` when `ρ` lives in universe `v`. Task 4412 owns its proof.
- `MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v}` (module
  `Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs`): the
  unitarizable-constituent step of VII.1.3. Take an actual maximal proper rational parabolic
  `P = MN` and an irreducible supercuspidal `ρ` of `M(F)` without a unitary central
  character. Suppose that `i_P ρ` is reducible and has a unitary central character. Then
  `i_P ρ` has an irreducible unitarizable subrepresentation or quotient `W`.

The universes are those of the conclusion: `u` for the field and `v` for the carrier of `ρ`.
No further hypothesis is added.

## Relation to the published nine-premise reduction

Worker 1714 published `maximalLeviSupercuspidalUnitarizableConstituent_of_geometricLemma`
(module `Langlands.Representation.Exponents.MaximalLeviUnitarizableConstituentReduction`). It
derives the conclusion from nine premises. The Library now proves six of them as theorems:
the geometric lemma, maximal-Levi containment, the cone complement, the self-normalizer,
unimodularity and the standard-cocharacter statement. This module uses those six theorems.
The other three premises are length two (VI.5.4), Casselman's criterion (VII.1.2) and
Jacquet's admissibility theorem (VI.2.2). The module derives each of them from the two
premises above through published reductions.

There is one difference from the published reduction. It uses only the sufficiency half of
Casselman's criterion, `ArbitraryParabolicCasselmanSufficiencyStatement` (module
`Langlands.Representation.Exponents.CasselmanSufficiencyReduction`). The full criterion is an
"if and only if". The constituent step only uses the direction "positive exponents imply
square-integrable modulo the centre". The Library reduces that direction to the joint
statement alone. For this reason the module restates the final assembly step with the
sufficiency statement instead of the full criterion.

## The proof

### `maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent_sufficiency`

Premises: `MaximalLeviSupercuspidalPositiveConstituentStatement.{u, v}`,
`ArbitraryParabolicCasselmanSufficiencyStatement.{u, max u v}` and
`RationalPointsIrreducibleAdmissibleStatement.{u, max u v}`. Conclusion: the target. This is
the published `maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent` with
the sufficiency statement in place of the full criterion. Unimodularity and the standard
cocharacter are no longer premises: they are the published theorems.

- The positive-constituent statement gives an irreducible subrepresentation or quotient `W`
  of `i_P ρ`. Along every actual rational parabolic and compatible root presentation, every
  normalized Jacquet exponent of `W` has real part in the strictly positive root cone.
- `W` has a unitary central character. It comes from that of `i_P ρ` through
  `unitaryCentralCharacterOfInjective` or `unitaryCentralCharacterOfSurjective` (module
  `Langlands.Representation.Exponents.JacquetNontrivialityTransfer`), depending on whether
  `W` is a subrepresentation or a quotient.
- `W` is admissible by the admissibility premise.
- `rationalSquareIntegrableUnimodularForm` (module
  `Langlands.Representation.Exponents.ArbitraryParabolicUnitarity`) gives an invariant
  positive form on `W` (Renard IV.3.2). Its modular-character input is the published theorem
  `RationalPointFamily.rationalReductiveUnimodularity` applied to the published
  `standardCocharacter`. The Hausdorff property of `G(F)` comes from `rationalPoint_t2Space`.
  Its remaining input is square-integrability modulo the centre for every Haar measure on
  `G(F)/Z(G(F))`. The sufficiency statement supplies it from admissibility, the unitary
  central character and the positivity of the exponents.

### `maximalLeviSupercuspidalLengthTwo_of_jointBasis_fixedLevel`

Premises: the joint statement at `u` and (KF) at `{u, max u v}`. Conclusion:
`MaximalLeviSupercuspidalInductionLengthTwoStatement.{u, v}` (Renard VI.5.4, (VII.1.3.2)). It
composes three published reductions:

- `representedCuspidalRemainderSplitting_of_fixedLevelFiniteness` (module
  `Langlands.Representation.Exponents.RepresentedCuspidalRemainderSplittingReduction`) at
  universes `{u, max u v}`. Its premises are (KF), the joint statement and the published
  theorems `parabolicDynamic`, `smoothMaximalSplitTorusConjugacy`, `standardCocharacter` and
  `relativeRootSystem`.
- `maximalLeviSupercuspidalLengthBound_of_cuspidalSplitting` (module
  `Langlands.Representation.Exponents.MaximalLeviSupercuspidalGeometricReduction`).
- `maximalLeviSupercuspidalLengthTwo_of_lengthBound` (module
  `Langlands.Representation.Exponents.MaximalLeviSupercuspidalLengthTwoReduction`).

### `maximalLeviSupercuspidalUnitarizableConstituent_of_jointBasis_fixedLevel`

The main theorem applies the first auxiliary theorem to three inputs.

- Positive constituent: the published `maximalLeviSupercuspidalPositiveConstituent_of_levi`
  applied to two published reductions.
  - `maximalLeviSupercuspidalExponentTransfer_of_geometricLemma`, with the published theorems
    `representedGeometricLemma` and `maximalLeviContainment`.
  - `maximalLeviSupercuspidalLeviPositiveConstituent_of_geometricLemma`, with
    `representedGeometricLemma`, the length-two statement from the second auxiliary theorem,
    and the published theorems `maximalLeviConeComplement`, `parabolicSelfNormalizer` and
    `centerSplitComponentCompactness`.
- Casselman sufficiency: the published
  `arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis` applied to the joint
  statement, at universes `{u, max u v}`.
- Admissibility: the published `rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum`
  (module `Langlands.Representation.Aubert.General.IrreducibleAdmissibleOfDatum`) applied to
  `rationalPointsJacquetCartanDatum_of` (module
  `Langlands.Representation.Aubert.General.RationalJacquetCartanDatum`). The latter takes the
  joint statement and the published theorems `standardCocharacter` and
  `standardParabolicOrder`.

The module uses no `sorry` and no new axioms. Its axioms are `propext`, `Classical.choice`
and `Quot.sound`.

## Provenance

Renard, *Représentations des groupes réductifs p-adiques* (2026), VII.1.3, proof (printed
pp.224–226, PDF pp.230–232). If `ρ` has no unitary central character, Renard shows that one
of the two constituents of `i_P ρ` satisfies Casselman's criterion VII.1.2. That constituent
is square-integrable modulo the centre, hence unitary (IV.3.2). The proof uses that `i_P ρ`
has length two (VI.5.4) and that irreducible representations are admissible (VI.2.2). The
split into the two open premises follows the published Library reductions listed above. It
is internal and is not taken from the literature.
