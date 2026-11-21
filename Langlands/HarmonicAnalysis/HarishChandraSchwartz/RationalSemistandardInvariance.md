# Waldspurger's invariant smooth spectral families

Waldspurger (2003), VI.3 (printed pp. 305–306), requires the section
at the Weyl-conjugate orbit and target parabolic to equal the normalized
V.3 comparison applied to the source section. `IsWeylInvariant` imposes
that equality at every actual inducing representative, in the same
coefficient fiber as the actual conjugate representative. The
comparison uses `WeylSectionComparisonData`, conditional on its displayed
`WeylSections.ClosedSectionComparisonStatement` at each compact lift.

The equality transporter uses the literal all-test Levi conjugacy
condition. `exists_lift` uses the compact-representative hypothesis to
cover every Weyl element and every parabolic with the conjugate Levi.
`target_transports` identifies the target orbit, and
`isWeylInvariant_iff` writes the same predicate with the relative
Weyl element explicit. The condition is imposed for all compact lifts.
Smooth sections already satisfy the canonical transport law for
inducing isomorphisms, including all self-twists.

The actual invariant submodule inherits smoothness and finite support
from `rationalSemistandardThetaSmoothSections`. The comparison maps
are complex linear and intertwine the actions in the actual coefficient
fibers. These facts give closure under the linear operations and the
full product-group action. Restricting that action gives the invariant
object in the canonical smooth category by the open stabilizers of
the underlying families.

The restriction to `rationalStandardThetaSmoothSections` is the
published `rationalStandardFullSmoothRestrict` on the underlying
family. It uses the exact discrete-series and compact-model comparison
premises of that map.
