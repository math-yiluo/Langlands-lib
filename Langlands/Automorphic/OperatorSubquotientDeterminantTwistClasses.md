# Determinant transport of actual quotient maps and classes

This internal construction transports maps and classes of actual
`OperatorSubquotient` representations by the existing finite-order determinant
multiplier. The number field has arbitrary universe, the rank is any natural
number and coefficients are complex. Finite order is explicit. The imported
`Intertwiner` abbreviation from `OperatorSubquotientCMTransportClasses` is the
general whole-action complex-linear intertwiner; its type requires no CM-field
instance. No CM-field hypothesis is imposed here.

`Intertwiner.determinantTwist` is conjugation of a supplied genuine quotient
intertwiner by the actual source and target quotient determinant equivalences.
Inverse covariance at the source, intertwining at the same concrete determinant
operator automorphism and forward covariance at the target prove its
whole-action intertwining law. Its exact application formulas hold on every
vector and on vectors written using the surjective determinant equivalence.
Cancellation of actual middle equivalences proves identity and composition
laws. Applying the forward application formula twice proves naturality through
the canonical inverse-character whole-action equivalences. This comparison
uses actual maps between dependent quotient presentations.

`Equivalence.determinantTwist` retains the actual conjugated linear equivalence
and the proved intertwining law. Its application, underlying-intertwiner,
identity, composition and inverse formulas follow from the same linear inverse
identities. Its finite restriction has the same map on the entire quotient
carrier, with the displayed exact application formula.

`determinantTwist_equivalence_iff` preserves and reflects existence of a genuine
whole-action equivalence. Preservation uses the constructed transported map.
Reflection transports a supplied equivalence by the inverse character and
composes with the canonical inverse-character equivalences at both ends.
`IsoClass.determinantTwist` therefore descends by `Quotient.lift` to the existing
whole-action quotient of actual representations. Quotient induction and the
canonical inverse-character equivalence prove cancellation on classes.
Applying this result to the inverse character and using its double-inverse
identity proves cancellation in the other order. `IsoClass.determinantTwistEquiv`
is the resulting permutation, with inverse given by the inverse character.
Injectivity and equality reflection follow from this actual permutation.

Provenance is internal: the actual induced quotient determinant maps and
covariance, the existing inverse-character equivalences, Mathlib's genuine
intertwiners and representation equivalences, and the existing quotient
setoid. The conjugation and descent route is the one implemented for CM
quotient transport, now with distinct character and inverse-character maps.
No new identification with original literature is claimed.

The construction adds no quotient evaluation or topology, continuity of
arbitrary intertwiners, selection of tensor factors, character identity/product
action law, central-character or cusp predicate on arbitrary quotients, or
nonzero, irreducible or spectral existence assertion.
