# Strict exponent spectra of tempered representations

Author: Worker 17.

This internal construction identifies the normalized Jacquet spectrum of a
normalized-exponent tempered representation with its strictly positive part
when every proper unitary Jacquet part vanishes. It retains the original
characters, actual parabolic, rational Levi, matching geometric radical,
multiplication isomorphism, split component and compatible root presentation.

`positiveJacquetExponents` is the subset of the actual normalized Jacquet
exponent set whose normalized real part lies in that presentation's strictly
positive cone. Its membership characterization and inclusion into the original
spectrum are definitional. The equivalence
`positiveJacquetExponentsEquivOfUnitaryVanishing` maps each original exponent
to this positive spectrum with the same character. Its inverse forgets the
positivity certificate. Both composites preserve the character, hence are
identities of the corresponding subtypes.

The positivity certificate is proved by contradiction. Temperedness puts the
specified exponent's normalized real part in the nonnegative cone. If it is
outside the positive cone, `boundaryUnitaryJacquetWitness` constructs an
actual proper outer parabolic, rational Levi, matching radical and split
component with a unitary normalized Jacquet exponent of the original
representation. Its unitary Jacquet part is nonzero. Applying the global
vanishing hypothesis to those exact constructed data is a contradiction.
The argument also tests the full parabolic: properness is required of the
constructed witness, not of the originally specified parabolic.

The final theorem proves that the existing
`HasPositiveRepresentedJacquetExponents` condition is equivalent, for a
tempered representation, to vanishing of every actual proper unitary Jacquet
part. The reverse implication is the preceding positivity argument. For the
forward implication, temperedness supplies a compatible presentation at each
specified triple. Strict positivity and the already proved exclusion of zero
from a proper parabolic's positive cone imply unitary-part vanishing by
`unitaryJacquetPart_eq_bot_of_positive_exponents`.

This is derived internal work for the boundary step in Renard VII.2.4. Field
and representation-carrier universes remain independent. The local-field,
canonical rational-point topology, local-compactness and nonarchimedean-group
instances are retained. The local finite type instance is available from
connected reductivity in the intended application. No central character,
finite length, irreducibility or additional geometric-existence hypothesis
is needed. In particular, the presentation coverage used here is part of
the published normalized-exponent temperedness predicate.

No analytic square-integrability assertion or version of Casselman's
criterion is assumed or proved in this module. The exact published
`TemperedSquareIntegrableUnitaryPartStatement` remains a separate proof
obligation requiring the independently owned Casselman criterion together
with the already constructed unitary central-character data.
