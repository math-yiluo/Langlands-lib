# A finite dimension bound for a finite-type scheme over a field

`FiniteTopologicalDimension X` means that the topological Krull dimension of the
scheme is bounded by some natural number. The derived theorem
`finiteTopologicalDimension` establishes this for every quasi-compact scheme
locally of finite type over a field, in arbitrary universe.

A finite-type field algebra is a quotient of a polynomial ring on finitely many
variables. Surjectivity bounds its Krull dimension by that of the polynomial
ring, which is the number of variables. On an affine chart, each scheme stalk is
the localization of the coordinate ring at its corresponding prime ideal. Its
dimension is the height of that prime, hence bounded by the chart's coordinate
ring dimension.

Quasi-compactness supplies a finite affine cover. The maximum of its natural
chart bounds bounds all stalk dimensions. The existing general
`FieldSmoothTopologicalKrullDim.topologicalKrullDim_le_of_stalk` lemma then bounds
the topological dimension; that lemma has no smoothness hypothesis. It uses a
closed point in each irreducible closed subset and the equality between stalk
dimension and point coheight. This is an internal adapter for the support
induction in the two-ample-bundle Serre vanishing task.
