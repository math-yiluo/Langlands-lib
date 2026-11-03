# The actual distribution character map on the exact finite-length K0

This is an internal derived interface for the published character realization
and injectivity proofs. It introduces no new original-literature assertion.
The group and representation carrier universes remain independent.

For a Hausdorff, locally compact, totally disconnected topological group with
its Borel measurable structure and a regular Haar measure, assume explicitly
that every finite-length smooth complex representation in the selected carrier
universe is admissible. `exactK0DistributionCharacter` chooses the integer-linear
map supplied by `exactK0CharacterRealization`. Its domain is the actual
`SmoothRep.FiniteLengthGrothendieckGroup`, with all short exact sequence
relations. Its codomain is the space of actual distributions.

`exactK0DistributionCharacter_ofRepresentation` is the chosen map's
specification: on a finite-length object it equals the genuine distribution
character of its action. `exactK0DistributionCharacter_injective` applies
`exactK0CharacterInjectivity` to that specification.
`ofRepresentation_eq_iff_distribution_eq` then applies injectivity in one
direction and the map in the other. The two supplied admissibility proofs agree
with the generic admissibility premise by proof irrelevance.

The direct proof dependencies are
`Langlands.Character.exactK0CharacterRealization` and
`Langlands.Character.exactK0CharacterInjectivity`. The former uses
`distributionShortExactAdditivity`; the latter uses
`finiteFamilyLinearIndependence`, the actual irreducible isomorphism classes and
`SmoothRep.irreducibleGrothendieckStatement`. Thus this interface uses character
independence and the Jordan–Hölder description of the exact finite-length
quotient through those published proofs. It does not supply the explicit
finite-length admissibility premise for any particular reductive group, nor an
induced representation comparison or Weyl conjugacy theorem.
