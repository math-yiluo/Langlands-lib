# Detecting invariant opens on rational points

This internal module connects membership of rational points to the equality of
scheme opens used by `SchemeAction.IsInvariantOpen`. Work over any algebraically
closed field `k : Type u`.

`opens_eq_of_rationalPoints` says that opens of a scheme locally of finite type
over `k` agree when they have the same rational points. Every closed point is
rational. If an open were not contained in the other, its intersection with the
closed complement would be a nonempty locally closed set in a Jacobson space,
so would contain a closed point, contradicting the premise.

`RationalOpenMembership` requires, for every rational group point and rational
target point, that membership in an open is equivalent before and after applying
the actual action. When the group and target are locally of finite type,
`isInvariantOpen_iff_rationalOpenMembership` proves that this predicate is
exactly `IsInvariantOpen`: equality of inverse-image opens under the actual
action morphism and the second projection. Apply the preceding open-detection
lemma to the product. A rational point of that product is the pair of its
projections, and the action on those projections is its composite with the
action morphism. The converse follows by evaluating the equality of opens.

The argument uses the published actual scheme-action and invariant-open APIs,
Mathlib's Jacobson property for locally finite type schemes, and its rational
section attached to a closed point over an algebraically closed field.
No reducedness, smoothness, separatedness, or connectedness is required.
This bridge can support the invariant affine cover argument once its rational
stability and affine-neighbourhood constructions are proved; it does not prove
the cover or the parent flag step.
