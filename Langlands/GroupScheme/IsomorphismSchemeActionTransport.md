# Inverse-precomposition actions under transport

This internal construction is derived from the all-test local-family,
supplied Isom representative, target-postcomposition and base-change
interfaces. It proves compatibility identities for the existing
constructors.

At an acted parameter point, the entire universal isomorphism family is
the family at the original point twisted by the inverse acting point.
The proof evaluates after every refinement and applies the defining
evaluation identity for the canonical action.

Postcomposing the target by an actual group-scheme isomorphism retains
the parameter scheme. The action on that parameter is unchanged:
evaluation of the new universal family is evaluation of the old family
followed by the target isomorphism. Therefore source-side inverse
precomposition commutes with this target change. The outer-quotient
constructor retains the class scheme and class morphism and transfers
invariance and the unique same-test acting point by this equality.

Restricting an isomorphism family to a new base commutes with twisting
by a point of the pulled-back acting group. This follows from the
natural point comparisons for the group pullbacks and their
compatibility with the pulled-back automorphic action.

Classification of a restricted family is its original classification
transported by the actual pullback adjunction. This proves the
corresponding action identity for `GroupIsomorphismScheme.baseChange`.
For every test over the new base, the action point on the pullback
parameter is the adjoint image of the action point on the original
parameter, with its acting point converted by the natural group-point
comparison. The proof uses the family identity for the action,
compatibility of twisting with restriction, and the classification
bijection.

All tests and bases are arbitrary; the statements assume the supplied
representative and automorphic action. No independent representability,
quotient existence, pinned classification or descent theorem is asserted.
