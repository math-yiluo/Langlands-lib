# Simple roots of the Euclidean arrangement

`positiveSimpleRoots` takes the indecomposable roots of a positive system. This is the ambient-space version of the simple-root construction in `GMFamilies`.

The finite positive set generates the same additive monoid as its indecomposable elements. For a regular point, two distinct indecomposable roots have nonpositive inner product. Otherwise the reflection integers and the Cauchy–Schwarz inequality force a root difference, whose sign decomposes one of the roots. The inner-product criterion for independence of an obtuse family in a common open half-space then gives linear independence.
The same generators span `span ℝ (↑R : Set E)`, since a regular point gives each root or its negative positive sign. `neg_mem_rootSet` obtains that negative from the reflection of a root in itself.

The basis property is the root-system input described in Arthur, *An introduction to the trace formula*, §5, printed p. 25, and used for the denominators in §17, printed p. 94. The Lean module derives it from `IsRootSet` in the Euclidean model. The retained source is `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
