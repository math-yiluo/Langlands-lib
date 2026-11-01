# Refinements and cut inclusion

This internal combinatorial helper identifies refinements of a fixed positive
ordered block shape with finer shapes, including rank zero. Its intended use is
the finite cancellation in Aubert's Theorem 1.7(3), printed p.2183 of the 1995
paper. The helper itself is derived from the Library's block-coordinate results.

Flattening preserves the coarse block label, so its cuts contain all coarse
cuts. Conversely, restrict the fine block-label map to each coarse block and
apply `monotoneBlockShape` to its nonempty consecutive fibers. The resulting
refinements have exactly the fine shape's equal-block relation. The cut/Weyl
correspondence shows that this relation determines the shape. Restriction to each
coarse block also proves injectivity of flattening. These arguments apply to
empty coordinate types without a positive-rank hypothesis.
