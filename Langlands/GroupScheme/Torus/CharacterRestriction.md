# Character restriction along test-scheme maps

This is an internal construction derived from the published Cartier relative-Hom
restriction and the multiplicative-group base-change isomorphisms. Its purpose is
to provide compositional character pullback when comparing different splitting fields.
It adds no assumptions to the definition of an induced torus and does not itself
assert the Weil decomposition.

For a commutative group scheme `T` over a scheme `S`, `characterLattice.relativeEquiv`
identifies relative homomorphisms `T_Q → (Gm_S)_Q` with actual characters of `T_Q`,
by postcomposition with `Gm.commBaseChangeIso Q.hom`. This is an abbreviation for
`Cartier.characterHomEquiv`. The additive map `characterLattice.restriction T a`
reuses the map of `Cartier.characterHomFunctor`, which conjugates `Cartier.restrict`
by those equivalences. Its identity and composition laws follow from Cartier
restriction's laws.

The theorem `gm_compIso` reuses `Cartier.gmBaseChange_comp`, whose proof uses the
units models on every test scheme. The canonical
iterated-pullback comparison preserves projection to the original multiplicative
group, and therefore preserves the same Laurent coordinate and its unit. This yields
`restriction_eq`: restriction is ordinary character base change precomposed with
the canonical domain comparison. Consequently `restriction_bijective` applies to
field-valued tests whenever the lower base change of `T` is split, using the published
split-torus character-base-change bijectivity. No finiteness or Galois hypothesis on
the two test fields is required.

For an endomorphism `a : B → B` over `S`, `comparison_endomorphism` compares the
Cartier and descent comparisons by their pullback projections. It implies
`restriction_endomorphism`: restriction is the published `characterLattice.transport`.
In particular, taking `B = Spec E` and `a = Spec σ` identifies this restriction with
the actual character Galois representation. All constructions preserve the universe
parameter and allow the trivial torus.
