# The affine apartment map in unramified descent

This internal consequence of the published valuation-descent constructions
equips `UnramifiedBuildingDescent.descentPoint` with a real affine structure.
It is partial progress toward `UnramifiedApartmentDescentStatement`; the
carrier comparison and injectivity of restriction on fixed apartment points
are explicit premises. This module does not assert unconditional descent.

The lower apartment is that of an arbitrary supplied `ValuationBuildingData B`.
The upper apartment is an equipollence class for the scalar extension of a
torus `T`, whose extension is a maximal split torus. A map `f : B.S → T`
induces `descentCocharacterMap` on real cocharacters. The hypotheses identify
the lower carrier with the restrictions of Galois-fixed upper points and assert
that this restriction is injective on fixed points.

Translation by the push-forward of a lower real cocharacter preserves Galois
fixedness, by `galoisCocharacterAction_descentCocharacterMap`. The published
torus-then-field restriction translation lemma identifies its restriction
with the corresponding lower translate. Uniqueness of the fixed lift therefore
gives `descentPoint_val_mk_vadd`.

If a lower cocharacter lies in the common root annihilator, its translation
fixes the lower point. The same uniqueness forces its push-forward to fix the
upper lift. The valuation stabilizer characterization puts that push-forward
in the upper root annihilator. Thus the cocharacter map descends to a linear
map of reduced translation spaces. Quotient induction proves that
`descentPoint` is affine with that linear part. Its injectivity and fixed
image follow from the corresponding published properties of `descentPoint`.

This proof is derived from the Library definitions and translation lemmas,
rather than a new direct formalization of a passage of Kaletha–Prasad.
