# Common domination of two actual z-extensions

`Langlands.GroupScheme.zExtensionCommonDomination` proves the unchanged
proposition `Langlands.GroupScheme.ZExtensionCommonDominationStatement`.
For every field and connected reductive group scheme `G`, it takes two
supplied actual z-extensions `z` and `t` and produces an actual z-extension
`w` and maps from `w.H` to `z.H` and `t.H`, both commuting with their
projections to `G`.

The proof applies `zExtensionMorphismDomination` with source and target
both equal to `G` and with homomorphism `𝟙 G`. That theorem constructs the
actual extension and both maps. Its first commuting equality is already
the required one. Its second equality has right-hand side `w.p ≫ 𝟙 G`,
which simplifies to `w.p` by the right identity law for composition.

This is the internal identity specialization of the morphism-compatible
domination theorem. It gives the existence-and-commutation consequence of
KP Fact 11.4.2 described in `ZExtensionRefinementStatement.md`; the imported
theorem supplies the actual fiber-product construction and its complete
z-extension structure. No common extension or commuting equality is an
input, and the proof adds no field hypothesis.
