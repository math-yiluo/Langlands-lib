# Galois discrepancies preserving an actual torus

This internal construction compares an actual group-scheme isomorphism over an
extension field with its Galois pullback. It is derived from the existing
pullback, canonical descent and character-transport interfaces.

For groups `G,H` over `k`, `groupIso E σ` is the Galois pullback of `E` followed
by `E.symm`, an actual automorphism of `G_L`. For ground-field commutative groups
`D,T`, `pulledTorusIso t σ` conjugates the base-changed isomorphism
`t : D_L ≅ T_L` by the two canonical descent isomorphisms in the category of
commutative group schemes. Its forward and inverse maps are precisely
`galoisHomTransport` applied to the two original maps, and the categorical
isomorphism construction supplies both inverse laws. `torusIso t σ` then
composes it with `t.symm`.

If inclusions `i : D → G` and `j : T → H` form an actual square with `E,t`,
`pulled_square` proves the same square after Galois pullback using `pullHom_comp`
and `pullHom_map`. `square` composes it with the inverse original square to show
that the discrepancy automorphism preserves the actual source torus. Two
private categorical lemmas isolate the inverse-square cancellation and the
composition of the two squares before specializing to group schemes.

`split_character_fixed` uses surjectivity of character base change for a split
torus and fixedness of base-changed characters. `torusIso_character` identifies
pullback by the discrepancy torus automorphism with the inverse Galois action
on the target characters, conjugated through `t`. Its proof applies
`galoisHomTransport_comp` to an inverse translate of the character, cancels the
two Galois actions, and uses fixedness of all source characters.

The inverse in this formula is dictated by the order “Galois pullback followed
by the original inverse.” It is relevant to the contravariant character action.
No special-linear automorphism classification or matrix formula is asserted
here. There is no characteristic, finite-degree, Galois-extension, or rank
restriction; the maps use every `k`-automorphism of the extension field.
