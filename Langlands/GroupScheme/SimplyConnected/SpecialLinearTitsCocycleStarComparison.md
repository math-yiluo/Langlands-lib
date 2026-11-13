# The based root action of the coordinate discrepancy

This internal helper compares the full root action of the actual coordinate
discrepancy with the inverse ordinary Galois action at its finite stage.
Its two final equivalences identify fixedness of every simple vertex, and
movement of some simple vertex, with the corresponding properties of the
original Tits star action for any specified lift of the stage Galois element.
This supplies the action comparison needed for the matrix cases in the parent
statement; it does not supply their matrix classification.

The contravariant root equivalence of the pinned presentation has character map
given by precomposition with its torus isomorphism. Injectivity of roots shows
that its index equivalence is exactly the inverse index equivalence of the
pinned isomorphism, hence it preserves the chosen bases. The character formula
then identifies the full discrepancy action with conjugation of the inverse
ordinary Galois action. The published naturality of based projection gives the
intertwining equality for their based representatives. The definitions
`discrepancyRootAut` and `discrepancyBasedAction` are the root equivalence
induced by the actual torus-preserving discrepancy and its canonical based
projection, respectively.

`discrepancyBasedAction_index` spells out that intertwining on simple-root
indices using the pinned index equivalence. Bijectivity of that equivalence
identifies fixedness of all coordinate simple roots with fixedness for the
inverse stage star action. The stage action is a group homomorphism, so an
element and its inverse fix exactly the same simple vertices. Finally,
`stage_fixes_iff_star` uses the retained finite-to-absolute base equivalence and
`Presentation.star_vertex` for the supplied lift. Composing these three
equivalences proves `discrepancyBasedAction_fixes_iff_star`. Its classical
negation proves `discrepancyBasedAction_moves_iff_star`.

These are derived categorical and root-datum comparisons of existing Library
constructions; no new original-literature classification is asserted.
The presentation, actual group and torus isomorphisms, and original
`TitsIndexData` are retained throughout. The module is universe polymorphic,
uses no characteristic or positive-rank restriction, and uses no downstream
outer-type-A or Kneser--Tits result.
