# Largest split subtori of commutative affine groups

This is a derived construction for the split-part step in the common-centralizer
argument. It uses the published theorem
`exists_largestCentralSplitTorus` from `Rational.SplitComponentProof`.
No new result from the literature is assumed.

For a commutative group scheme `H` over an arbitrary field,
`IsLargestSplitSubtorus i` says that `i : A → H` is a closed split subtorus
and that every group-scheme homomorphism from any split torus to `H` factors
uniquely through `i`. These are actual homomorphisms of group schemes.
The factorization property covers homomorphisms that are not embeddings.

The theorem `exists_largestSplitSubtorus` constructs such an `i` when the
total space of `H` is affine and its structure morphism is locally of finite
type. Commutativity makes every homomorphism to `H` central on every test
scheme, so the published largest-central-split-torus construction supplies
the factorization. The closed immersion is a monomorphism, which proves
uniqueness.

The Lean proof then derives maximality by using the universal property to
construct the inverse of any proposed enlargement. Conversely, maximality
forces the factorization through the constructed largest split subtorus
to be an isomorphism, so every maximal split torus of `H` has the same
universal property. Two largest split subtori are consequently isomorphic
over `H`.

The last theorem derives affineness and local finite type for any closed
commutative subgroup of an affine group locally of finite type, and
applies the construction to that subgroup. In particular, it applies to a
closed maximal torus in a connected reductive group. The result proves
maximality inside the commutative subgroup; it does not assert ambient
maximality in a reductive group or any parabolic centralizer containment.

All declarations are general in the field and its universe. The file
does not use rational-point density or replace subgroup-scheme morphisms
by rational-point maps.
