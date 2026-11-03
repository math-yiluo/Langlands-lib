# Smoothness from a smooth open subgroup

This derived unit defines `HasSmoothOpenSubgroup` using an actual group homomorphism
that is an open immersion from a smooth group scheme. For a group scheme locally
of finite type over a field, this property is equivalent to smoothness.

Over an algebraically closed field, the proof chooses a closed point of a nonempty
smooth locus. Any closed point can be translated to that point by a group
translation isomorphism. Smoothness is invariant under that isomorphism. If the
smooth locus had a nonempty closed complement, the Jacobson property would supply
a closed point there, contradicting the translation argument. This adapts the
argument in Mathlib's `AlgebraicGeometry.Group.Smooth` to a group that is not
assumed reduced; the nonempty smooth locus is provided explicitly instead.

Over an arbitrary field, base change carries the given open subgroup to an open
subgroup over the algebraic closure. Its smoothness makes the ambient smooth
locus nonempty. The preceding translation argument proves smoothness there, and
fpqc descent along the field extension proves smoothness over the original field.
The converse uses the identity homomorphism as the open subgroup.

Combining this result with `isOpenImmersion_of_fullLie` proves
`smooth_of_fullLie_closed_subgroup`: a locally finite-type affine group with a
smooth closed subgroup surjecting on the actual Lie kernel is smooth. These are
supporting results; no semigroup intersection connectedness alternative is proved
here.
