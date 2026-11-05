# Gluing geometrically irreducible morphisms across an open cover

These are internal auxiliary lemmas for finite-type generic geometric
irreducibility spreading. Their proof is elementary topology and actual
scheme pullback geometry; no additional literature theorem is asserted.

An open cover by irreducible subsets with every pair intersecting has an
irreducible union, provided the cover index is nonempty. Given two nonempty
open sets, select cover members meeting them. Irreducibility of the first
member propagates the first open into the second member, and irreducibility
of the second gives a point in both opens. A member supplies nonemptiness.
The scheme version applies this argument to the open images of the cover maps.

For a morphism f and an open cover of its source, assume each member's
composite to the base is geometrically irreducible and that every pair of
member images intersects every fibre of f. Then f is geometrically irreducible.
After an arbitrary field base change, the pulled-back cover members are
irreducible by the hypothesis and pullback-pasting isomorphisms. To find a point
in a pairwise overlap, choose a point of the field spectrum, an overlap point
over its image in the original base, and a point of the scheme pullback lifting
this compatible pair. The ranges of the pulled-back cover maps are preimages
of the original ranges, so the lifted point lies in both. The topological
criterion applies. No finite cover, finite type, quasi-separatedness,
flatness or openness of f is assumed.

The companion assembly module constructs the finite cover and arranges
geometric irreducibility and overlap nonemptiness after shrinking around the
generic point.

The same gluing criterion is provided for an unbundled family of open
immersions whose images cover the source. The proof bundles that family as
an open cover and applies the preceding criterion. This permits removal
of the indices whose restricted source pieces are empty.
