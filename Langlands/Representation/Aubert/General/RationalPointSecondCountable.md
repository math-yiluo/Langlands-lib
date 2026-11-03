# Second countability of actual rational points

Author: Worker 53.

This is an internal consequence of Mathlib's local-field topology results and
the published finite-coordinate topology of affine group-scheme points. It
provides a topological input for the actual standard-parabolic modular-character
comparison. It does not assert unimodularity or a modular-character formula.

`localField_secondCountable` proves that a field in any universe, equipped with
the displayed `ValuativeRel`, topology, and `IsNonarchimedeanLocalField`
instances, is second countable. The proof equips the given topological additive
group with its right uniformity. The local-field valuation has rank one.
Mathlib's scoped `Valued` construction therefore gives a nontrivial norm with
the same topology. Local compactness makes that normed field proper, and
Mathlib's proper-space second-countability instance gives the conclusion. The
topology in the conclusion is the original topology.

`rationalPoint_secondCountable` applies to an affine group scheme over such a
field whose structure map is locally of finite type. Its conclusion uses
exactly `RationalPointFamily.pointTopology` on the identity-test carrier
`RationalPoint k G.X`. The existing
`GroupScheme.affinePointsSecondCountableTopology` gives second countability of
the base-coefficient affine points. The proof transports this property through
`affinePointsRingPointHomeomorph` and `rationalPointHomeomorph`. These are the
published comparisons of the evaluation topologies on the actual point
carriers.

`reductiveRationalPoint_secondCountable` specializes this result to the published
`IsConnectedReductive G`. Its affine structure map is a field of that predicate;
smoothness supplies the locally finite type instance. Thus it introduces no
second-countability premise into the rational-parabolic modulus target.
