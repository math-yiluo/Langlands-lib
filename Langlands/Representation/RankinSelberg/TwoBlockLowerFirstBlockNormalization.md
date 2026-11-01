# Integral normalization of the lower mixed Haar

This derived support for JPSS (1983), Section 4.9, printed pages 416–418,
uses the actual lower mixed subgroup and its published coordinates. The
construction keeps the canonical p-adic structures and both positive block
sizes. It chooses `lowerMixedHaar` independently of any supplied rectangular
additive Haar measure, as the Haar measure assigning mass one to the compact
open inverse image of `GL_(t+1)(O)`.

The integral-coordinate lemma is proved entry by entry for an arbitrary
subring of a field. The diagonal blocks of an integral lower product and its
inverse are integral. Its lower-left block, multiplied by the integral inverse
first block, recovers the integral radical coordinate. Conversely the integral
rectangle and integral invertible diagonal blocks give integral entries in the
lower product and its explicit inverse.

An integral invertible first block has determinant norm one: its determinant
and inverse determinant are integral, their absolute values are at most one,
and their product is one. Thus restriction normalization gives the integral
subgroup of the norm-one first block mass one. The second unipotent integral
subgroup already has mass one. The coordinate preimage of the lower mixed
integral subgroup is the product of these two sets and the rectangular cube.

Haar uniqueness identifies the actual coordinate product measure with a scalar
multiple of `lowerMixedHaar`. Evaluation on this compact open subgroup shows
that the scalar is exactly the supplied rectangular cube mass. Uniqueness in
the other direction transfers right invariance from the product Haar to the
normalized measure. Closedness of the lower mixed subgroup and the fixed
bi-invariant ambient Haar then give compatible quotient existence.

These are internal normalization and measure-existence results motivated by
the lower mixed group in JPSS equation (2). The module proves no quotient
measure tower or integration formula.
