# Actual lattice maps of root-datum homomorphisms

This internal prerequisite identifies the contravariant coweight map from its
actual character map. It also supplies a maximal-torus comparison used in the
necessity direction of the integral coroot criterion. All base fields have
arbitrary universe `u`; the two root index types have independent universes.
No classification, cover-existence, or simple-connectedness theorem is used.

`CommGroupScheme.isIso_of_groupHom_isIso` writes the inverse of an underlying
group-scheme isomorphism in the additive notation used for commutative group
homomorphisms. Its two inverse identities are the original identities with the
notation changed.

`IsMaximalTorus.isIso_factor_of_isIso` considers a commuting square
`i ≫ φ = groupHom t ≫ j`. Here `i` is a maximal-torus embedding, `φ` is an
isomorphism of ambient groups, and `j` is a closed embedding of a torus.
Transport of maximality along `φ` and the definition of maximality imply that
`groupHom t` is an isomorphism. The preceding lemma gives `IsIso t` in the
commutative category. The target torus need not be maximal or split.

For `P` on the actual character and cocharacter lattices of `T` and `Q` on
those of `T'`, `RootDatumHom.coweightMap_apply_of_weightMap` assumes that their
pairings are `latticePairing T` and `latticePairing T'`. If a root-pairing
homomorphism `f : P → Q` has weight map `χ ↦ t ≫ χ` for `t : T' → T`, then its
coweight map is `ν ↦ ν ≫ t`. The proof uses injectivity of the perfect pairing,
the transpose identity in `RootPairing.Hom`, and associativity of composition
in the definition of the actual lattice pairing. It requires neither finite
root sets nor reductivity or maximality.

`RootDatumHom.surjective_coweightMap_of_isIso` then proves surjectivity when
`t` is an isomorphism: a preimage of `ν` is `ν ≫ inv t`.
`RootDatumHom.injective_coweightMap_of_isIso` proves injectivity by cancellation
of `t`. The definition `RootDatumHom.coweightMapEquivOfIso` packages these
facts into an integral linear equivalence from the cocharacter lattice of
`T'` to that of `T`, using `LinearEquiv.ofBijective`. Its forward map is
definitionally `f.coweightMap`, as the apply lemma records; the formula above
identifies it with postcomposition by `t`, and its inverse with
postcomposition by `inv t`. This construction attaches the equivalence to the
given root-datum morphism, including its specified coweight map.

These statements and the equivalence
concern the full integral lattices, with no rationalization. This module does
not assert existence of root data or central isogenies, or prove the coroot
criterion or the host field-extension theorem.
