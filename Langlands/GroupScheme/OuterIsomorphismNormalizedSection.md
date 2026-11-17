# Outer quotients from normalized sections on all tests

This internal adapter formalizes the Yoneda step in the split pinned
construction suggested by Brian Conrad, *Reductive group schemes* (2014),
Theorem 7.1.9(3) and its proof, pp.245–246, registered as
`conrad-2014-reductive-group-schemes`. It is a derived construction. It
retains an actual normalized parameter scheme, its section into the supplied
isomorphism scheme, and the unique decomposition on every test as inputs.
It does not construct a pinned parameter scheme or prove that decomposition
for reductive groups.

Let `I` represent isomorphisms from supplied group schemes `G` to `H` over
`S`, and let `a` be an automorphic action of a supplied group scheme `A` on
`G`. For an actual relative scheme `Q` and a morphism
`s : Q ⟶ I.parameter`, `sectionOrbitMap` is the actual morphism
`A.X ⊗ Q ⟶ I.parameter` taking `(d,q)` to the inverse-precomposition action
of `d` on `s(q)`.

Assume that this formula gives a bijection from
`(T ⟶ A.X) × (T ⟶ Q)` to `T ⟶ I.parameter` for every relative scheme
test `T`. The theorem `sectionOrbitMap_isIso` proves that the orbit morphism
is an isomorphism by the Yoneda criterion: uniqueness gives injectivity on
maps into the product, and existence gives surjectivity. No restriction to
affine, reduced, connected, or base-valued tests is made.

The action multiplication law proves `sectionOrbitMap_equivariant`.
`normalizedProductIso` packages the resulting product presentation.
Assuming that `A` is flat and quasi-compact over `S`,
`outerOfNormalizedSection` applies `outerOfProduct` to obtain an
`OuterIsomorphismScheme I a`. In particular the class morphism is flat,
surjective, and quasi-compact, and equal classes have a unique difference
in `A` on the same test scheme. Neither a lift to `G` nor finiteness of `Q`
is assumed.
