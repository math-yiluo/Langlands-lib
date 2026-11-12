# Points of a represented presheaf

Author: Worker 107.

This internal construction compares `Points ((schemeYoneda S).obj U)` with the underlying
point set of the actual scheme `U.left`. It is derived from the definitions in
`SpacePoints.lean` and Mathlib's universal residue-field factorization. It is prerequisite
infrastructure for comparing the geometric fibre in Conrad's Lemma 5.1 with scheme atlases.

`FieldPoint.schemeValue` evaluates the represented morphism at the unique point of its
field spectrum. Agreement over a common field implies equality of the resulting scheme
points. Every field-valued morphism factors through the residue field of its image; this
factorization supplies the quotient equality with the canonical `schemePoint`.
Consequently `schemePointsEquiv` identifies the quotient points with scheme points.

The comparison is natural in all scheme morphisms (`schemePointsTo_map` and
`schemePoint_naturality`). This module establishes a set equivalence only; the
comparison of topologies is a separate construction. No connected-component
constructibility claim is made here.
