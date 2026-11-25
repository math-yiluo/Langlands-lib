# Actual inner points for arbitrary pinned atlas transitions

This internal construction first records compatibility between direct
pullback of an actual isomorphism and refinement of its natural local
family. It follows by computing the two coordinates of lifted test points.
Consequently, evaluating an automorphic action at a relative point commutes
with arbitrary direct pullback.

Actual relative points glue across any small disjoint decomposition of
their parameter scheme: the inverse of the coproduct isomorphism followed
by the coproduct of the component points gives the point, including its
base equation. Its restrictions recover the supplied points. Equality of
actual group-scheme maps is detected on these components, so an
automorphism induced by relative points on all components is induced by
their assembled point. No uniqueness of the component points is required.

The provenance is internal composition of pullback evaluation, the
local-isomorphism equivalence, evaluated actions and disjoint component
assembly from the existing Library.

The companion `AffinePinnedTransitionInner` construction proves innerness
of inverse corrected chart transitions by transporting the supplied
full-centre quotient and its action to a pinned model and back. The natural
pinned comparison remains an explicit input. This module supplies the actual
point assembly used to extend that result across the arbitrary atlas; it
does not assert atlas-transition innerness or the final existence theorem.
