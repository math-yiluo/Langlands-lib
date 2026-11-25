# Actual Weyl and orbit descent for the normalized comparisons

`ClosedWeylDescentStatement` concerns the actual intrinsic semistandard
sections (`RationalSemistandardOrbitSections`) using the special compact of the fixed maximal split
torus and the split-central quotient Haar at the exact trace-normalized
Weil scale. It includes `ClosedSectionComparisonStatement` for
every displayed compact lift. `liftClass` is the class of that lift in the
published left target-Levi `SemistandardWeylConjugacyQuotient`. Equality of
classes uses the exact criterion `n' * n⁻¹ ∈ W^M'` on the Weyl elements.
It gives a canonical inducing isomorphism for the conjugate objects by
actual inner conjugation in the target Levi. `changeLiftFiber` applies
this isomorphism to the intrinsic normalized product coefficient fiber.
`LiftFiberIndependence` states equality of certified normalized maps after
this transport for all source representatives and all vectors.

`QuotientRealization` states that a compatible compact lift for each
quotient element gives a coherent smooth comparison at that element.
`liftClass_surjective` constructs such representatives from the published
`HasWeylRepresentatives` condition on this same compact. The comparison
retains the actual compact levels and realizes the certified normalized
values at the chosen lift. With any other lift
of the same element, each smooth comparison satisfying the actual value
property agrees after `recenterTarget`, which changes the base within the
actual target orbit. `SourceBaseIndependence` uses the corresponding
published smooth recentering on both source and target. The new source
base is any actual representative of the source orbit with the same
split-central quotient Haar normalization.

For a lift in the actual relative Weyl subgroup of the Levi and the same
source and target parabolic, `innerIso` is the actual inner inducing
isomorphism. `ClosedInnerCovarianceStatement` states that the actual
normalized comparison is this canonical coefficient transport.
`automaticInnerCovariance` proves the corresponding equation for every
smooth coherent section with the canonical transport by applying its
coherence under the actual inducing isomorphism. `normalizedInnerCovariance`
applies the stated identification of the maps to give the equation for the
actual normalized comparison.

The mathematical assertions use Waldspurger, *La formule de Plancherel
pour les groupes p-adiques* (2003), I.1 printed pp. 238 and 240/PDF pp. 4
and 6, III.1 (3) printed p. 265/PDF p. 31, V.2 printed p. 293/PDF p. 59,
V.3 printed p. 295/PDF p. 61, VI.1
printed pp. 295–296/PDF pp. 61–62, and the automatic `W^M` covariance in
VI.3 printed p. 306/PDF p. 72. The left quotient used here is the exact
relative Weyl equality transporter quotient already in the Library.
