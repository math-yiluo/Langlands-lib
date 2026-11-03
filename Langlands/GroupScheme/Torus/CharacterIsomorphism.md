# Detecting isomorphisms of split tori on actual characters

Author: Worker 1375.

This internal construction works over every base scheme `S : Scheme u`.
It uses the product presentation in `IsSplitTorus` and the actual character
lattice `Hom(T, 𝔾_m)`. It requires no field, coordinates on an integral
lattice, separability, or isogeny hypothesis.

`IsSplitTorus.hom_ext_of_characters` says that actual characters separate
homomorphisms into a split torus. After choosing a splitting isomorphism
`T ≅ 𝔾_m^I`, equality after every character implies equality after each
coordinate projection of that product, hence equality of the original
homomorphisms. The domain can be any commutative group scheme.

`IsSplitTorus.isoOfBijectiveCharacterPullback` takes split commutative group
schemes `T`, `T'`, an actual homomorphism `t : T → T'`, and bijectivity of
`χ ↦ t ≫ χ` on their actual characters. It constructs an isomorphism with
forward morphism exactly `t`. The companion hom lemma records this equality.
The existence proof is
`IsSplitTorus.exists_iso_of_bijective_characterPullback`; the named
isomorphism chooses a witness together with the proof that its hom is `t`.

Choose a presentation `e : T ≅ 𝔾_m^I`. Surjectivity of character pullback
provides a character `ψ_i` of `T'` whose composite with `t` is the
`i`-th projection after `e`. The sum of `ψ_i` followed by the `i`-th
coordinate inclusion is a morphism `T' → 𝔾_m^I`. Compose it with `e.inv`
to obtain `g : T' → T`. The finite-product identity
`∑ projection_i ≫ inclusion_i = identity` proves `t ≫ g = identity`.

To prove `g ≫ t = identity`, test against every character of `T'`.
Precomposing the desired equality with `t` reduces it to the preceding
identity. Injectivity of character pullback cancels this precomposition,
and character separation for the split torus `T'` identifies the two
morphisms. Thus both inverse identities hold as actual morphism identities.

`characterPullback_bijective_of_isIso` proves the converse for arbitrary
commutative group schemes: pullback along an isomorphism has inverse
pullback along its inverse. The final
`IsSplitTorus.isIso_iff_bijective_characterPullback` combines the two
directions for split tori.

This is a direct internal deduction from the published finite-product
and commutative group-scheme interfaces. For the central-isogeny
root-datum task, it supplies the equivalence between isomorphism of the
torus restriction and bijectivity of its actual character map. Relating
that torus restriction to the ambient group homomorphism remains a
separate geometric obligation.

The character-separation wrapper reuses the published
`IsSplitTorus.hom_ext_characters` from `Rational/RelativeWeylCharacterAction`.
