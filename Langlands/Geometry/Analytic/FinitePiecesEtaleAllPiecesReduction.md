# Finite-to-all transport reduced to full-domain flatness and tensor comparison

Author: Worker 310.

`finitePiecesEtaleAllPieces_of_flatness_tensor` proves the existing
`FinitePiecesEtaleAllPiecesStatement` from two explicit prerequisites:
`Domain.FlatnessStatement` and the finite ordinary tensor comparison
statement over the fixed field. This is a conditional reduction; it
does not prove the unconditional target until those premises are supplied.
The theorem preserves independent `u/v/w` universes and the original
finite open neighborhoods in the finite-family hypothesis.

Select one target piece of the finite family through the image point,
and use `IsFiniteOver` to obtain its actual recognized inverse image.
For any arbitrary recognized target piece and any supplied recognized
inverse image and source point, the net axiom gives a common recognized
target piece through the image point inside both target pieces.
`IsFiniteOver` supplies its recognized inverse image, whose literal
locus is the corresponding restriction of each original source piece.

The nested pullback theorem first preserves étaleness from the chosen
finite-family piece to the common piece, and then reflects it to the
arbitrary piece. The full chart restriction equations identify the
source points. Injectivity of the arbitrary recognized source chart
identifies the projected point with the point supplied in the target
quantifier. Uniqueness of recognized subsets with the same literal
locus also transfers the finite-map certificate to the supplied source
piece. These steps satisfy all recognized-subset, inverse-image and
chart-point quantifiers of the unchanged Library target.

The proof is internally derived from the Library's recognition net,
finite-over definition, full-domain pullbacks and the accompanying
algebraic transport lemmas. Berkovich's Proposition 3.2.3 motivates the
finite-to-all target, but this implemented reduction uses prime-local
faithful-flat reflection through a common recognized subpiece, rather
than asserting the source's finite-cover flatness lemma as an input.
No Hausdorff ambient-space, strict-radius or nontrivial-valuation
assumption is added.
