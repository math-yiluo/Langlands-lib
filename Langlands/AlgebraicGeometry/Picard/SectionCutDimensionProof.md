# Dimension bounds for actual principal vanishing loci

For the upper bound, the closure-image map embeds the poset of
irreducible closed subsets of `Z` into that of `T`. Closedness places
all images inside `Z`. They are strictly below the irreducible closed
set `T`, because `Z` is proper. Extend the map to `WithTop` by sending
the extra top element to `T`. Strict monotonicity and the formula for
the Krull dimension of `WithTop` give the claimed inequality. If the
poset of irreducible closed subsets of `Z` is empty, its dimension is
bottom and the inequality is immediate.

For the lower bound, pull back the global basic open along the
canonical local-spectrum map. The published formula for its action
on sections identifies the pullback with the basic open of the germ.
The quotient map kills that germ, so the composite from the quotient
spectrum has image in the vanishing locus. Both the quotient-spectrum
map and the local-spectrum map are embeddings; the composite remains
inducing after restricting its codomain to the vanishing locus.
Dimension is monotone under inducing maps, and the topological
dimension of an affine spectrum equals its ring Krull dimension.
