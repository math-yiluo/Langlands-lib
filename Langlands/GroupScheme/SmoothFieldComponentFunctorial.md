# Normality and field base change of smooth field identity components

This internal derived construction extends `SmoothFieldComponent` to normality
on every test scheme and canonical comparison under arbitrary extension of the
ground field. The ambient smooth group may be nonaffine, disconnected, or not
quasi-compact. No additional hypotheses are imposed on it.

`isNormal_range_inclusion` proves that the range subgroup functor of the actual
identity-component inclusion is normal. The conjugation morphism from the
ambient group times its identity component lands in the identity component:
each fibre of the first projection is connected and contains the value of the
unit section, whose conjugate is the unit. Its continuous image lies in the
unit's connected component. Lifting conjugation through the open immersion
then gives the required conjugation lift on every test scheme.

`isoOfIsOpenImmersion H j` identifies a connected open and closed subgroup with
the constructed identity component, compatibly with both inclusions. It uses
the published topological characterization `IdentityComponent.range_eq_identitySet`
and factors the two inclusion homomorphisms through one another.

`baseChangeIso H φ` canonically identifies the actual base change of
`SmoothFieldComponent.group H` with the identity component of the base-changed
group for every field homomorphism `φ`. The pulled-back inclusion is open and
closed, and its source remains connected by geometric connectedness. The
preceding characterization supplies the isomorphism. The two final equalities
record compatibility with the actual inclusions into the base-changed ambient
group.

The construction and proof pattern are derived from the published affine
`IdentityComponent` normality and field-base-change argument, applied to the
nonaffine construction with the same geometric properties. This module does
not assert preservation of the unipotent radical.
