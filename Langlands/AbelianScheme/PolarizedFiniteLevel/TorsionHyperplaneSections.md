# Actual torsion sections in projective hyperplanes

This is an internal adapter for the published
`CubicTorsionHyperplaneBoundStatement`. Its definition
`TorsionHyperplaneSections i f n` is exactly the subtype counted there:
actual sections killed by multiplication by `n`, evaluated at the closed
point of `Spec K`, whose image under `i` has homogeneous prime containing
the degree-one polynomial `f`.

`FullLevel.hyperplaneCoordinateEquiv` restricts the existing actual linear
equivalence `FullLevel.fibreCoordinates` to that incidence subtype. Its
source is a subtype of `Fin (2*g) -> ZMod n`, with incidence tested after
applying the supplied full-level coordinate map. It introduces no freely
chosen point configuration.

`FullLevel.card_fibreLevel` proves that the actual torsion module at every
specified geometric point has cardinality `n^(2*g)`. It transports natural
cardinality through the existing coordinate equivalence, then uses the
cardinality of a finite function type and `ZMod n`. This identity is valid
also at level zero, using the convention that the natural cardinality of an
infinite type is zero. `FullLevel.finite_fibreLevel` separately proves
finiteness for positive level by transport from the finite coordinate type.
Both results use the supplied full level and assert no unconditional
torsion-rank or full-level-existence theorem.

`FullLevel.card_hyperplaneSections_le` injects the actual incidence subtype
into the finite torsion module, giving the total-cardinality bound
`n^(2*g)`. `FullLevel.card_hyperplaneSections_le_of_sq_le` derives the
published numerical bound when
`n^2 <= 6^g*d*g!`: positive `g` gives
`n^(2*g) = n^2 * n^(2*g-2)`, and multiplication preserves the assumed
inequality. These results need no embedding, nondegeneracy or cubic-bundle
comparison because they only count a subset of all torsion sections.

This module does not prove the published geometric statement for unrestricted
positive level. The remaining range requires the actual geometric estimate;
the additional numerical condition in the last helper is not a hypothesis
added to that target. The definitions and proofs here are internal
consequences of the published full-level coordinates and Mathlib's natural
cardinality API, rather than a formalization of the intersection argument
in GIT Proposition 7.7.
