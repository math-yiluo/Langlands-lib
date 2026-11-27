# Real-place control for representatives in a quadratic opposite-Borel torus

`IsQuadraticOppositeBorelTorus.exists_realLocallyTrivialRepresentative`
fixes a maximal torus obtained from a pair of opposite Borels over the
quadratic extension. A cocycle trivial on each real pullback has a
representative in that torus with the same real triviality on the
original cover.

The regular cocharacter for the Borel pair supplies the open cell
`U × T × U⁻` over the covering field. The nonidentity automorphism
interchanges the two unipotent factors. For a twisted cocycle value in
this cell, uniqueness of the coordinates gives the cocycle identity
for the torus coordinate. Twisting by the first unipotent coordinate
gives the image of that torus cocycle.

At a complex place above a real place, a local trivializing cochain
takes the twisted cocycle value to the identity. Continuity of the
cell coordinates and the torus coboundary neighbourhood supply an open
set of acceptable cochains. Weak approximation at the set of these
complex places gives one global cochain in all the opens. Membership
in the open cell over any one completion descends to the covering
field. If there are no such places, Zariski density of twisted values
gives a cochain whose value lies in the cell.

At a real place with a real place above it, the completion extension
has degree one. Its inverse gives an embedding of the covering field
into the base completion over the number field, hence a section of the
full pullback cover. Evaluating the cocycle against this section
trivializes it.

This implements Platonov and Rapinchuk, *Algebraic Groups and Number
Theory* (1994), Lemma 6.28, printed pp. 369–370.
