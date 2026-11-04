# Homomorphisms from affine unipotent groups to arbitrary tori

Over every field `k : Type u`, an affine group scheme satisfying the existing
representation-theoretic `IsUnipotent` predicate has only the zero homomorphism
to any group scheme satisfying the existing `IsTorus` predicate. The target
torus need not split over `k`. There is no characteristic, perfectness,
smoothness, connectedness, or finite-type hypothesis.

This is an internal consequence of the published split-target vanishing
theorem, preservation of affine unipotence by field extension, and faithfulness
of pullback along a field extension. It extends the split-target interface in
`Torus/UnipotentHom`; it is distinct from the reverse-direction results in
`Unipotent/TorusHom` and `Rational/TorusSplitUnipotentHom`.

The proof of `IsUnipotent.hom_eq_zero_of_isTorus` chooses the splitting field
provided by the unchanged `IsTorus` predicate. The base-changed source remains
unipotent by `IsUnipotent.baseChange`. The published
`IsUnipotent.hom_eq_zero_of_isSplitTorus` makes the base-changed homomorphism
zero. Faithfulness of `Over.pullback` along that field extension reflects
equality of the underlying scheme morphisms, and faithfulness of the group
forgetful functor yields equality of the original homomorphisms.

The all-test point and range statements follow from this equality with the
actual zero homomorphism. `IsUnipotent.uniqueHomToTorus` packages that
homomorphism and its uniqueness as a `Unique` structure. A composite through
such a torus is also zero.

Finally, `IsUnipotent.range_eq_bot_of_range_le_isTorus` applies to two monic
inclusions in any ambient group. The existing range-containment factorization
gives a homomorphism from the affine unipotent source to the torus. Its
vanishing makes the original inclusion zero, so its range is the identity
subgroup functor on every scheme test.

These results require unipotence of the given source. They do not establish
unipotence of an arbitrary closed subgroup or of an intersection, and they do
not prove maximality preservation in a quotient or the host rational-conjugacy
statement.
