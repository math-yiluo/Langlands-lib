# Descending actual Bernstein components to the original carrier

This derived construction addresses the carrier-universe step in the proof
of Renard VI.7.2. It retains actual Bernstein inertial-support uniqueness
and a supplied decomposition in the saturated carrier as explicit inputs.
It proves no unconditional support theorem or decomposition.

`bernsteinBlockProperty_of_injectiveIntertwiner` transfers the original
block property from an object in the saturated carrier to an object of
the original carrier admitting an actual injective intertwiner into it.
Every actual irreducible subquotient of the source lifts to an irreducible
subquotient of the target. Applying the saturated block property gives
exactly the lifted support relation required by `bernsteinBlockProperty`.

`bernsteinDescendedCofanIsColimit` pulls a spanning family of actual invariant
block subspaces back along a representation equivalence. The pulled
subspaces retain the original carrier universe, span the original object,
and satisfy its original block property. Actual support uniqueness excludes
common irreducible subquotients of differently indexed components.
The published invariant-subspace summation construction gives their
coproduct universal property.

`isBernsteinCoproductOfComponents_of_equiv` applies this construction to the
images of the legs of a supplied component coproduct. These images inherit
their block properties as quotients and span the coproduct vertex.
`isBernsteinCoproductOfComponents_of_injectiveIntertwiner` first splits the
actual invariant image inside the larger decomposed object, using the
published conditional subrepresentation theorem, then descends along the
actual source-to-image equivalence.

The field and source-carrier universes remain independent. The larger
carrier is exactly their maximum; the inertial quotient may exceed both,
and no existence of coproducts indexed in that larger quotient universe
is assumed. All properties, support relations and indices are the original
published Bernstein definitions. The finite cuspidal embedding, the
decomposition of its target and unconditional support uniqueness remain
separate obligations.
