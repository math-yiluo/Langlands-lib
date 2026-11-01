# Finite equalities of actual relative homomorphisms

Let `S` be a locally noetherian scheme, let `G` and `H` be actual commutative
group schemes over `S`, and let `I` be a finite index type in its own universe.
Assume a scheme `E/S` and a supplied natural isomorphism from the underlying
relative Hom presheaf of `G` and `H` to the restricted Yoneda presheaf of `E`.
The restriction is to the full category of all locally noetherian schemes over
`S`, with all its morphisms. The relative Hom functor and its restriction maps
are the existing Cartier constructions using actual group-scheme base change.

Given families `p,q : I → (G ⟶ H)` of global homomorphisms,
`relativeHomEquationSection` encodes the identity-base-change of each global
homomorphism at the allowed identity test `S → S`. The product universal
property combines these maps into a section `S → E^I` in schemes over `S`.
`relativeHomEquationSection_decode` proves that restricting and decoding this
section at any allowed `T/S` returns exactly the actual base change of each
`p_i`. Its proof uses naturality of the supplied comparison and the existing
`restrict_baseChange_map` identity for actual Cartier restrictions.

`relativeHomEquation_condition_iff` shows that the two sections agree after a
map `T → S` if and only if every basechanged `p_i` equals the corresponding
basechanged `q_i`. One direction projects and decodes. The converse uses the
injectivity of the comparison and extensionality of maps to a product.

`relativeHomEquationLocus` is the actual equalizer of these sections in
schemes over `S`, and `relativeHomEquationLocusInclusion` is its equalizer map
to the identity object over `S`. If `E/S` is separated, the finite power `E^I`
is separated over `S` by the previously constructed finite-product geometry.
The equalizer inclusion, and hence the locus structural morphism to `S`, is a
closed immersion. A closed immersion is locally of finite type, so the locus
is locally noetherian. This includes the empty finite index type. No local
finite type hypothesis on `E/S` is used.

`relativeHomEquationLocusHomEquiv` gives an actual equivalence between morphisms
`T → locus` and pairs consisting of a morphism `T → S` over `S` and proofs of
all the basechanged equalities. Its inverse is the equalizer lift, and the
inverse laws follow from the equalizer universal property.
`relativeHomEquationLocus_nonempty_iff` removes the unique structural-map datum:
a morphism to the locus exists exactly when every basechanged equality holds.
The identity object is terminal in the category over `S`.

This is an internal categorical construction from the existing relative Hom
functor, its canonical restriction identities, and the scheme equalizer and
finite-product geometry. It supplies no existence proof for the relative Hom
representative. It imposes equalities between supplied global homomorphisms;
it does not construct arbitrary families of homomorphisms or assume that the
finite power itself is a locally noetherian test. No universal tuple at that
power is needed because the homomorphisms being compared are global data.
