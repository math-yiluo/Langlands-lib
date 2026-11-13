# Actual finite unramified integer overlap components

For a nonarchimedean local field `F` and an actual finite Galois intermediate
field `E` in its separable closure with `ArithmeticUnramified F E`, this
construction applies the derived integral tensor equivalence to the actual
map `Spec (extensionIntegers F E) → Spec (baseIntegers F)`.

The existing `galoisIndexEquiv F E` enumerates the field automorphisms by the
small finite type `Fin [E:F]`. Reindexing the tensor equivalence gives a
product with that index type. The general commutative-ring component
construction then gives an actual isomorphism from the finite coproduct of
`Spec (extensionIntegers F E)` to the double overlap.

The first projection on each component is the identity. The second is
exactly the spectrum map of the corresponding actual integer automorphism.
The proofs reuse the ring component identities and the tensor formula.
This is an internal application and asserts no group-scheme semilinear
isomorphisms or descent datum.
