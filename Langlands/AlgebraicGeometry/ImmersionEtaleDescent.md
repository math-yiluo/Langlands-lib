# Immersions descend under surjective étale base change

This internal derivation proves that a scheme morphism is an immersion if its
base change by a surjective étale target morphism is an immersion. The input is
a supplied cartesian square. There are no affineness, quasi-compactness or
noetherian assumptions.

`rangeNeighbourhood` constructs the open coborder of the range from a supplied
proof that the range is locally closed. It uses only the topological condition,
before any immersion property of the scheme morphism is available.

The proof first uses the pullback point comparison to identify the range of the
base-changed map with the inverse image of the original range. A surjective
étale morphism is open, continuous and a quotient map. For an open continuous
map, inverse image commutes with closure and hence with coborder. The locally
closed original range follows because its coborder is open after this quotient
map.

The original morphism lifts to its open range neighbourhood, where its image is
closed. The lift's base change is an immersion: pasting its pullback square with
the open restriction square recovers the original supplied pullback, and the
comparison isomorphism transfers the immersion property. Its range is closed
by the pullback range formula. It is therefore a closed immersion. Closed
immersion descent along the restricted surjective étale map makes the original
lift a closed immersion. Composition with the open inclusion proves immersion.

The provenance is internal, using Mathlib's pullback, immersion and topological
interfaces and the Library's surjective étale descent for closed immersions.
No separate external-source translation is asserted.
