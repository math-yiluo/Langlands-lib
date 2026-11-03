# Eventual lifting of sections from an ample fibre

`ProperFibrePowerSectionLiftingStatement` is the degree-zero
section-surjectivity input for fixed-bundle ampleness spreading. For a
proper `f : X ⟶ S`, a locally noetherian base, a specified actual line
bundle `L`, and an arbitrary point `s`, assume the actual residue-field
fibre restriction of `L` is ample. The statement asks for one threshold
such that every section of every higher power on the fibre lifts over
the inverse image of some affine open neighbourhood of `s`.

The threshold is independent of the section; the neighbourhood and the
lift may depend on it. The fibre module is the actual pullback of
`tensorPow L.obj n`. The Library's actual tensor-power pullback
isomorphism identifies this with the corresponding power of the
restricted bundle. The equality of restrictions uses
`fibreNeighbourhoodSection`, which is the actual pullback-adjunction
unit followed by restriction to the whole fibre.

This is a derived neighbourhood formulation of the special case `F = O_X` of the surjectivity
conclusion in Stacks Project, Lemma 30.21.3, in
[Section 30.21, tag 02OF](https://stacks.math.columbia.edu/tag/02OF).
Apply that lemma after choosing an affine neighbourhood of `s`;
local noetherianity makes this neighbourhood noetherian. A section
in the stalk of the pushforward is represented on a neighbourhood.
Refining that neighbourhood to an affine open and restricting its
representative gives this formulation. No flatness assumption is
introduced. The source is retained as
`stacks-noetherian-fibre-section-lifting-2026-11-03`, files `02OF.html`
and `02OF.txt`, Lemma 30.21.3 and its proof. The page reports no comments,
and no project errata note for this source was present when read.
The source's proof uses graded Serre vanishing and formal
functions, rather than flat cohomology-and-base-change.

This file defines a proposition only. It supplies neither the lifting
proof nor the geometric step from lifted sections to ampleness.
