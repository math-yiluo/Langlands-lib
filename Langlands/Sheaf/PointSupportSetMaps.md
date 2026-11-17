# Support transport by natural maps of underlying sets

This internal extension of `PointSupport` allows a natural transformation between
the underlying set presheaves of module presheaves. It assumes preservation of
zero but does not assume additivity or linearity.

The actual filtered-colimit criterion for equality of germs represents a zero
germ by a restriction that is zero on a point neighborhood. Naturality carries
that restriction to a zero restriction in the target. Consequently such maps
shrink the actual germ support and carry compactly supported sections to
compactly supported sections. A natural zero-preserving set section of a sheaf
morphism therefore supplies a surjection on compactly supported sections.

The construction uses only the imported Library and Mathlib APIs. It makes no
new assertion about the original literature or about geometric separation.
