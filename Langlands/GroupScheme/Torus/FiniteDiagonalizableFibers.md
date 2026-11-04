# Dominant residue fibers of finite diagonalizable factors

This internal construction uses the actual residue fields of the full group
algebra and the actual pullback of an arbitrary scheme over the base field.
The residue point maps into the diagonalizable group, and
`residueFiberInclusion` includes the scalar extension of the other factor into
their product. Its topological image is exactly the fiber over the selected
prime of the finite factor. These fibers cover the product, including when the
finite diagonalizable group has nilpotents.

For a dominant map from this product to an irreducible scheme, finiteness of the
prime spectrum gives a finite cover of the target by closures of the images of
the residue fibers. Irreducibility forces one closure to be the whole target.
The restricted map from the actual residue-field scalar extension is therefore
dominant into the original target.

The provenance is internal, using the proved residue-field results, Mathlib's
pullback image formula and the finite closed-cover criterion for irreducibility.
This contribution does not assert dominance into the scalar extension of the target,
pointed split-torus domination or maximal-torus conjugacy.
