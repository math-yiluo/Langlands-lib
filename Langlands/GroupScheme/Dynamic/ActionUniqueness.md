# Uniqueness and invariant morphisms for abstract dynamic subgroup functors

This internal supporting module works over an arbitrary base scheme S and on every
scheme T over S. Its actual multiplicative-group actions and dynamic subgroup
functors are the constructions in `Dynamic.Action`.

`AutomorphicAction.IsInvariantMorphism a f` means that the value of the actual
scheme morphism f is unchanged by the action on every test scheme. This
predicate permits an arbitrary acting group scheme and an arbitrary target
scheme over S.

For a multiplicative-group action on a separated group scheme G,
`IsOrbitExtension.unique` and `HasLimit.unique` give uniqueness of extensions and
limits. The extension proof applies the published
`AffineLine.hom_ext_of_unitInclusion` to the common orbit restriction. The limit
proof evaluates the equal extensions at zero.

A fixed point has its constant extension. If it also has identity limit, limit
uniqueness makes it the identity. Thus `centralizer_inf_unipotent_eq_bot`
identifies the intersection of the fixed and identity-limit functors with the
identity functor.

The invariant-morphism results require only that the target of f is separated;
they impose no separatedness on G. Composing an orbit extension with f agrees
on the multiplicative-group open with the constant morphism through its initial
value. The same affine-line uniqueness theorem identifies the two morphisms.
Evaluation at zero proves that f has equal values on a point and any orbit
limit. For a group homomorphism f, every point with identity limit therefore
maps to the identity. The last two theorems state this as an inclusion in the
preimage of the identity subgroup functor and as a trivial-image equality.

These are derived interfaces for the existing actual action and affine-line
constructions, using the previously proved separated-target extension
uniqueness. They use no new external theorem or geometric realization and do
not assert the cyclic relative-root comparison.
