# Group isomorphisms from a compatible covering family

This internal construction assembles actual local group-scheme
isomorphisms and applies the Library's fppf descent of independent natural
local isomorphisms. It is intended for the affine pinned charts used in the
general-base isomorphism argument of Conrad, *Reductive group schemes*
(2014), Proposition 6.2.11(2), pp.210–211.

Let `G,H` be group schemes over a scheme `S`, and let `pᵢ : Xᵢ → S` be
an arbitrary small family. The only covering hypothesis is that the map
from the disjoint union of all `Xᵢ` to `S` is flat, surjective and locally
of finite presentation. Suppose each member carries an actual isomorphism
`G × Xᵢ ≅ H × Xᵢ`. `CoverIsomorphism.IsCompatible` requires that these
isomorphisms agree after direct pullback to every common test of two
members over `S`. The canonical comparisons between iterated and direct
pullbacks are included in this equation.

`CoverIsomorphism.descend` produces an actual group-scheme isomorphism
over `S`. Its pullback to every member is exactly the supplied
isomorphism, and this recovery property uniquely determines it. The
groups, members and base need not be affine or quasi-compact.

The proof assembles the member isomorphisms over the disjoint union.
For any two points of that union over the same test scheme, their
inverse images in the individual components give two disjoint
decompositions. Refining by both decompositions reduces equality of the
pulled-back maps to the supplied compatibility equation. Evaluation
through the actual pullback projections identifies this equation with
independence of the associated natural local group isomorphism. The
published fppf descent then supplies the global isomorphism. Its exact
recovery and uniqueness follow from the component restrictions and
faithfulness of pullback along the single fppf map.

This is a general gluing adapter. It does not construct root lines,
pinnings or compatible local isomorphisms, and it does not assert the
full reductive-group theorem of that argument.
