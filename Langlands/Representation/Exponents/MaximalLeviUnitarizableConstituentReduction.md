# The unitarizable-constituent step of Renard VII.1.3 as a reduction

Author: Worker 1714. Module
`Langlands.Representation.Exponents.MaximalLeviUnitarizableConstituentReduction`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. It is an internal conditional reduction for
the proof of Renard VII.1.3. It puts together the published reductions of the two exponent
steps and Casselman's criterion.

## Statements

`MaximalLeviSupercuspidalUnitarizableConstituentReductionStatement` is the implication

```lean
RepresentedGeometricLemmaStatement.{u, v} →
  MaximalLeviContainmentStatement.{u} →
    MaximalLeviSupercuspidalInductionLengthTwoStatement.{u, v} →
      MaximalLeviConeComplementStatement.{u} →
        ParabolicSelfNormalizerStatement.{u} →
          ArbitraryParabolicCasselmanCriterionStatement.{u, max u v} →
            RationalPointsIrreducibleAdmissibleStatement.{u, max u v} →
              RationalPointFamily.RationalReductiveUnimodularityStatement.{u} →
                StandardCocharacterStatement.{u} →
                  MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v}
```

`maximalLeviSupercuspidalUnitarizableConstituent_of_geometricLemma` proves it. The nine
premises and the conclusion are published statements, used unchanged. None of the premises is
proved here.

- `RepresentedGeometricLemmaStatement`: the geometric lemma (Renard VI.5.1–VI.5.3) for
  represented parabolics. `r_Q ∘ i_P` is glued from the pieces of the double cosets
  `P(F) z Q(F)`.
- `MaximalLeviContainmentStatement`: let `P = MN` be an actual maximal proper rational
  parabolic. If the rational Levi `L` of an actual proper rational parabolic contains `M`,
  then `L = M`.
- `MaximalLeviSupercuspidalInductionLengthTwoStatement`: if `i_P ρ` is reducible, there is a
  short exact sequence `π₁ ↪ i_P ρ ↠ π₂` with `π₁` and `π₂` irreducible.
- `MaximalLeviConeComplementStatement`: let `P = MN` be an actual maximal proper parabolic
  with split component `A`. Take two parabolics with Levi factor `M`, with presentations for
  `A` whose positive cones both miss a nonzero `x ∈ X^*(A) ⊗ ℝ` that pairs to zero with the
  cocharacters central in `G`. Then the two parabolics have the same range in `G`, and so do
  their unipotent radicals.
- `ParabolicSelfNormalizerStatement`: the range of a parabolic subgroup is its own
  normalizer.
- `ArbitraryParabolicCasselmanCriterionStatement` (Renard VII.1.2), at representation universe
  `max u v`: an admissible representation of `G(F)` with a unitary central character is
  square-integrable modulo the centre for a Haar measure on `G(F)/Z(G(F))` if and only if,
  along every actual rational parabolic and compatible root presentation, every normalized
  Jacquet exponent has normalized real part in the strictly positive root cone.
- `RationalPointsIrreducibleAdmissibleStatement` (Jacquet, Renard VI.2.2), at universe
  `max u v`: every irreducible smooth representation of `G(F)` is admissible.
- `RationalPointFamily.RationalReductiveUnimodularityStatement`: given the
  standard-cocharacter statement, the modular character of `G(F)` is trivial.
- `StandardCocharacterStatement`: standard cocharacters exist, and each standard subgroup
  functor is the dynamic subgroup of every standard cocharacter.

The compactness of the centre modulo a split component, which the constituent step also
needs, is not a premise. It is the published theorem `centerSplitComponentCompactness`
(module `Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessProof`).

The conclusion `MaximalLeviSupercuspidalUnitarizableConstituentStatement` (module
`Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs`) is the
unitarizable-constituent step of VII.1.3. Take an actual maximal proper rational parabolic
`P = MN` and an irreducible supercuspidal `ρ` of `M(F)` with no unitary central character.
If `i_P ρ` is reducible and has a unitary central character, then it has an irreducible
unitarizable subrepresentation or quotient `W`.

## Auxiliary theorems

- `maximalLeviSupercuspidalPositiveConstituent_of_levi`: the transfer statement
  `MaximalLeviSupercuspidalExponentTransferStatement` and the constituent statement
  `MaximalLeviSupercuspidalLeviPositiveConstituentStatement` (both in module
  `Langlands.Representation.Exponents.MaximalLeviSupercuspidalLeviExponentStatements`) give
  the positive-constituent statement `MaximalLeviSupercuspidalPositiveConstituentStatement`.
  That statement gives an irreducible subrepresentation or quotient `W` of `i_P ρ` whose
  normalized Jacquet exponents along every actual rational parabolic and compatible root
  presentation have real part in the strictly positive root cone.
- `maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent`: the
  positive-constituent statement, Casselman's criterion, Jacquet's admissibility theorem,
  unimodularity and the standard-cocharacter statement give the conclusion.

## Provenance

Renard, VII.1.3, proof (printed pp.224–226, PDF pp.230–232). In the case of a non-unitary
central character of `ρ`, Renard shows that one of the two constituents `π₁`, `π₂` of
`i_P^G ρ` satisfies Casselman's criterion VII.1.2. That constituent is square-integrable
modulo the centre and therefore unitary (IV.3.2). Here the exponent part is split into the
constituent step and the transfer step, with published reductions
`maximalLeviSupercuspidalLeviPositiveConstituent_of_geometricLemma` (module
`Langlands.Representation.Exponents.MaximalLeviSupercuspidalLeviPositiveConstituentReduction`)
and `maximalLeviSupercuspidalExponentTransfer_of_geometricLemma` (module
`Langlands.Representation.Exponents.MaximalLeviSupercuspidalExponentTransferReduction`). The
grouping of the inputs into one implication is internal.

## The proof

- `maximalLeviSupercuspidalPositiveConstituent_of_levi`: the constituent statement gives `W`,
  together with its positivity along the parabolics with Levi factor `M` and its map to or
  from `i_P ρ`. The transfer statement, applied to that map and that positivity, gives
  positivity along every actual parabolic.
- `maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent`: the
  positive-constituent statement gives `W`.
  - `W` has a unitary central character: by `unitaryCentralCharacterOfInjective` or
    `unitaryCentralCharacterOfSurjective` (module
    `Langlands.Representation.Exponents.JacquetNontrivialityTransfer`), from that of `i_P ρ`.
  - `W` is admissible by Jacquet's theorem.
  - Casselman's criterion (`.mpr`) makes `W` square-integrable modulo the centre for every
    Haar measure on `G(F)/Z(G(F))`.
  - `rationalSquareIntegrableUnimodularForm` (module
    `Langlands.Representation.Exponents.ArbitraryParabolicUnitarity`) turns this into an
    invariant positive form on `W`. It uses the trivial modular character from the
    unimodularity statement, applied to the standard-cocharacter statement. So `W` is
    unitarizable.
- `maximalLeviSupercuspidalUnitarizableConstituent_of_geometricLemma` composes the four:
  - the transfer reduction, applied to the geometric lemma and the containment statement;
  - the constituent reduction, applied to the geometric lemma, the length-two statement, the
    cone complement statement, the self-normalizer statement and
    `centerSplitComponentCompactness`;
  - the two auxiliary theorems.
