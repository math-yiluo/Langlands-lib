# The universal morphism for actual affine finite-type Weil restriction

Worker 105 constructs the canonical morphism from the actual base change of
the finite-type affine Weil-restriction scheme to the original affine scheme.
The construction uses the universal tensor-valued algebra point and the existing
canonical tensor presentation of an actual scheme pullback.

For every actual test scheme over `Spec A`, pull back its map to the constructed
scheme and compose with this universal morphism. This gives an actual morphism
over `Spec B` and is natural in every test scheme. No affineness or finiteness
condition is imposed on the test scheme.

This is derived infrastructure for Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), Example 2.4, printed page 3. It does not yet
assert that the comparison is bijective for all test schemes. The original scheme
is affine and of finite type over `B`, and `B` is finite projective over the
arbitrary commutative ring `A`. There are no topology, faithfulness, field,
Noetherianity or finite-presentation assumptions.

The auxiliary projection identities identify the inverse tensor presentation's
first projection with `Spec` of the right tensor inclusion, and its second
projection with the specified `B`-structure map. The presentation is natural in
every map of test algebras. Its proof uses the two projections of the actual
pullback: the right tensor inclusion commutes with tensoring the test-algebra
map, while that tensor map preserves the left `B`-factor. These auxiliary laws
require only commutative algebras, without finite projectivity.

`affineWeilRestrictionCounit` uses the actual affine-coordinate equivalence to
turn the universal point into a morphism of schemes over `Spec B`, preceded by
the canonical presentation of the actual pullback. The comparison is its
composition with the actual pullback functor on morphisms. Its naturality is
the composition law for that functor and associativity. The universal property
on arbitrary test schemes remains a separate assertion and proof obligation.

Registered source: `conrad-2011-weil-grothendieck-adelic-points`, content SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
