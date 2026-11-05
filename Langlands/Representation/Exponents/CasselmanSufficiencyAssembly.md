# Sufficiency assembly for supplied actual standard presentations

Author: Worker 1682.

This internal supporting module assembles the represented-parabolic
positive-cone condition into the standard strict Jacquet criterion. It
does not prove the unconditional Casselman criterion.

`StandardCasselmanPresentation` records actual parabolic, Levi, radical
and split-component maps at a specified standard index. Its compatible
root presentation uses exactly the specified torus, generic cocharacter
and selected simple roots. The record also supplies the exact equality
between the radical point image and the standard unipotent subgroup.
The corresponding literal Levi equality follows by evaluating the
compatible all-test Levi equality on the field. The record is supplied
data; the module does not assert that such records exist.

`HasPositiveRepresentedJacquetExponents` names the all-parabolic
positive-cone hypothesis on the right of the published represented
Casselman statement, retaining every parabolic, Levi, radical, component,
presentation and exponent test. It does not include presentation
existence.

Given a family of matching standard presentations and the selected-root
valuation-one law on central torus points, the first theorem applies the
standard full-center exponent comparison at every index. The universal
represented cone hypothesis specializes to each of the actual maps in
the supplied family. The result is the strict bound for every standard
full-center exponent on its actual noncentral negative torus tests.

The last theorem assumes the strict Jacquet square-integrability
sufficiency proposition. The published standard-cocharacter theorem
supplies the semidirect decompositions used by that proposition. The
preceding strict bounds feed the arbitrary-carrier sufficiency adapter,
which handles the carrier universe by an actual universe lift and returns
square integrability for the original representation and the given Haar
measure on the actual central quotient.

All field and carrier universes remain independent. Actual standard
presentation existence, the selected-root law, the standard-cocharacter
proposition, radical closedness and analytic sufficiency remain supplied.
These are retained obligations, not assumptions added to the exact
Casselman target. The module asserts no necessity implication and no new
original-source equivalence.
