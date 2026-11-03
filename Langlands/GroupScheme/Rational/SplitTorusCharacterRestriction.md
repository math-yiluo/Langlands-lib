# Character restriction along monomorphisms of actual split tori

Author: Worker 1327.

This internal derivation transfers the published
`splitTorus.characterMap_surjective` from coordinate split tori to arbitrary
actual split tori. It holds over every field and in every universe, including
rank zero. A scheme monomorphism `f : A → T` induces a surjective restriction
map on integral characters.

Choose split presentations of `A` and `T` and conjugate `f` by those
presentations. The resulting morphism between standard split tori remains
a scheme monomorphism. The published coordinate-character surjectivity
theorem gives a character preimage there. Pull that character back through
the target presentation; the composition and identity laws of
`characterRestrict` show that it restricts to the prescribed original
character of `A`.

`IsSplitTorus.characterLift` is a chosen extension operator assigning such an
actual character of `T` to each prescribed character of `A`.
`characterRestrict_characterLift` proves that restricting the extension
recovers the original character. No additivity of this choice is asserted.

Right exactness of tensor products preserves surjectivity, giving the
corresponding results for the published rational and real character
restriction maps. The provenance is internal: the geometric content is
already proved by the group-algebra cokernel test in
`Rational.SplitTorusMonomorphism`. No new root-kernel or central-direction
comparison is asserted here.
