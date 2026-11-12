# Sheaves after composition of bases

Author: Worker 109.

This internal construction extends `BaseCompositionPresheaf` from actual
presheaves to actual fppf sheaves. It is derived from the published
`OriginalBaseTransport` total/fibre constructions, the fppf subcanonical
site of schemes, and Mathlib's sheaf conditions on a slice site. No external
literature assertion is claimed as proved here.

For any schemes `S,T : Scheme.{u}` and any morphism `g : S ⟶ T`,
`BaseComposition.sheaf g F` is the fppf sheaf over `T` whose sections on a
test `V/T` consist of a map `s : V.left ⟶ S`, a section of `F` over that
map, and the equation `s ≫ g = V.hom`. Its underlying presheaf is exactly
`BaseComposition.presheaf g F.obj`; there is no sheafification or change in
its sections. `sheafFunctor g` applies the already defined natural
transformation `map g` on morphisms and preserves identities and composition.
The constructions use all scheme tests and values in `Type (u+1)` at arbitrary
`u`, without a condition on `g`.

The proof has two parts. `isSheaf_totalPresheaf` starts with a compatible
family of total sections over an absolute covering sieve. Its structure
maps glue in the represented fppf sheaf of `S`. The inverse of
`Sieve.overEquiv` gives the corresponding covering sieve on the scheme with
that glued structure map. The published `totalFiberIso` converts the family
into compatible sections of the original relative sheaf, which then glue.
Uniqueness first identifies the two structure maps, using the represented
sheaf, and then the two original sections, using the original sheaf.

`fiberToRestriction` forgets the fibre equation on a section of an absolute
presheaf. `isSheaf_fiberPresheaf` uses continuity of `Over.forget S` to
restrict an absolute fppf sheaf to the relative site. It glues a family there
and verifies its prescribed structure-map equation by separatedness of the
restricted represented sheaf of `S`. The fibre inclusion then gives
uniqueness. Applying this result to the total presheaf and its projection
composed with the Yoneda image of `g` proves `isSheaf_presheaf` and yields
`sheaf`.

This module constructs fppf sheaves only. It does not establish representable
diagonals, an etale presentation, or transport of morphism properties and
finite type. Those algebraic-space and arithmetic obligations remain; the
unchanged unconditional adelic smooth-openness target is not proved here.
