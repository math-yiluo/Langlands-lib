# Corrected support on the actual homogeneous Jacquet cut complex

This internal assembly specializes `FilteredCutDiagram` to the actual normalized
Jacquet cut diagram. At a cut set `s`, the submodule is the actual image of
`correctedJacquetSupport T (shape s) C θ` evaluated at the normalized Jacquet
module of the given smooth representation `A`. The existing support-preservation
theorem for `cutJacquetMap` proves that these submodules form a subdiagram.
Thus the homogeneous support is a condition on the actual coordinate Jacquet
modules, preserved by the existing signed homogeneous differential.

Monotonicity in the Weyl support follows coordinatewise from the existing
corrected Jacquet support theorem. Empty support gives the zero homogeneous
submodule, and full support gives the whole homogeneous module. These statements
also hold when the coordinate set is empty. No rank restriction is imposed.

The coordinate carrier comparison identifies the quotient diagram modules with
the existing `cutSupportQuotient` carriers. Its transitions are the actual
Jacquet diagram transitions restricted to upper support and descended through
the pulled-back lower support. A separate comparison with the bundled
`cutSupportQuotientMap` morphisms remains an obligation.

A sequence of Weyl supports gives a sequence of actual submodules in every
homogeneous degree. An empty-to-full monotone finite segment is therefore an
exhaustive finite filtration. `correctedGradedEquiv` identifies its actual
adjacent quotient with the homogeneous product of coordinate support quotients.
The differential square is the specialization of the supported-diagram square.
In particular, every original exterior insertion sign is retained.

The last results transport injectivity and middle exactness across these
equivalences and apply `FiniteFilteredExactness` to lift them to the actual
Jacquet cut differential. They require injectivity or middle exactness on all
coordinate quotient diagrams in the finite segment. They establish neither
those graded hypotheses nor a geometric identification with orbit modules.
Injectivity uses the empty and full endpoints; the exactness lift also uses
monotonicity and the already proved square-zero identity. There is no claim of
exactness at a surviving terminal homology term.

The provenance is internal: the existing actual support images and transition
preservation, the supported-diagram quotient comparison, and finite filtered
linear algebra. The field and representation universes remain independent and
the actual induction, normalized Jacquet maps and supplied topology are retained.
