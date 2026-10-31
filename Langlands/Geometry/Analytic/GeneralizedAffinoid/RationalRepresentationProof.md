# Rational charts represent their loci against all presented affinoid tests

Author: Worker 1010.

The theorem
`Langlands.Analytic.PresentedAffinoidAlgebra.rationalRepresentation`
has the type `RationalRepresentationStatement.{u}` from
[RationalRepresentationStatement](RationalRepresentationStatement.md). Let
`K` be a complete ultrametric normed field, `A` a presented affinoid algebra
over `K` with arbitrary positive radii, and `d` a rational chart of `A`. Then
`Represents K d.baseMap d.locus` holds. No hypothesis on the valuation, the
radii, the arity of the chart, reducedness or nonvanishing of `A` is added.

The proof follows the source result named in the statement's Markdown:
Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
literature ID `berkovich-2009-trieste-analytic-spaces`, Definition 2.2.1 and
Exercise 2.2.2(ii), p.9. The statement itself is the derived presentation
formulation recorded there.

## Closedness and range

The first two clauses of `Represents` are published facts about the
underlying rational presentation.

- `RationalPresentation.isClosed_locus` gives that `d.locus` is closed.
- `RationalChart.range_comap_baseMap` states that the range of the spectrum
  comap along `d.baseMap` is `d.locus`. It is
  `RationalPresentation.range_spectrumMap` applied to `d.generates`.

## A test map sends the denominator to a unit

Let `R` be a presented affinoid algebra over `K` and `φ : A → R` a bounded
`K`-algebra homomorphism whose spectrum image lies in `d.locus`. Write `g`
for the denominator class and `f_j` for the numerator classes in `A`.

`RationalChart.isUnit_denominator_of_hasImageIn` shows that `φ(g)` is a unit
of `R`. For each point `y` of the spectrum of `R`, the comap of `y` along `φ`
lies in `d.locus`. The published `RationalPresentation.denominator_ne_zero`
uses `d.generates` to show that no point of the locus vanishes on `g`.
Hence `y(φ(g)) ≠ 0` for every `y`. The unit criterion, the second component
of `spectrumIdealCriterion K : SpectrumIdealCriterionStatement K`, then gives
that `φ(g)` is a unit.

## The fractions are spectrally bounded

Let `u` be the unit with `u = φ(g)` and set `b_j = u⁻¹ φ(f_j)`.

`RationalChart.spectrum_fraction_le` shows `y(b_j) ≤ d.radii j` for every
point `y` of the spectrum of `R`. The locus condition on the comap of `y`
reads `y(φ(f_j)) ≤ d.radii j * y(u)`. Multiplicativity of `y` gives
`y(u⁻¹) y(u) = 1`, so
`y(b_j) = y(u⁻¹) y(φ(f_j)) ≤ d.radii j * y(u⁻¹) y(u) = d.radii j`.

## Factorization

`RationalChart.existsUnique_factorization` proves the third clause.

1. Each `b_j` is spectrally bounded by the strictly positive radius
   `d.radii j`. The published `spectralPowerBound` turns this into a
   radius-`d.radii j` power bound `‖b_j ^ n‖ ≤ C (d.radii j)^n`.
2. `hasBoundedMonomials_iff_radiusBoundedPowers` combines these finitely many
   power bounds into the uniform weighted monomial bound
   `HasBoundedMonomials d.radii R b`.
3. By construction `φ(g) b_j = u u⁻¹ φ(f_j) = φ(f_j)`.
4. The published `RationalPresentation.existsUnique_extension`, with
   `d.generates`, these `b_j`, the monomial bound and these equations, gives
   exactly one bounded `K`-algebra homomorphism `ψ : d.algebra → R` with
   `ψ.comp d.baseMap = φ`.

Uniqueness comes from that published theorem and does not depend on the
choice of `b`. The edge cases need no separate treatment: for an empty
numerator tuple the monomial bound is vacuous, and a zero test algebra has
empty spectrum, so `φ(g)` is a unit there as well.

`RationalChart.represents` assembles the three clauses, and
`rationalRepresentation` applies it to every input of the statement.

## Dependencies

- `spectrumIdealCriterion` from
  [SpectrumIdealCriterionProof](SpectrumIdealCriterionProof.md).
- `spectralPowerBound` from
  [SpectralPowerBoundProof](SpectralPowerBoundProof.md).
- `RationalPresentation.isClosed_locus`, `RationalPresentation.range_spectrumMap`,
  `RationalPresentation.denominator_ne_zero` and
  `RationalPresentation.existsUnique_extension` from
  [RationalPresentation](RationalPresentation.md),
  [RationalSpectrum](RationalSpectrum.md) and
  [RationalExtension](RationalExtension.md).
- `hasBoundedMonomials_iff_radiusBoundedPowers` from
  [WeightedPowerBounds](../WeightedPowerBounds.md).

The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
