# Comparing the finite and pivot-coordinate special-linear tori

This internal adapter identifies the finite-coordinate diagonal torus used by the
special-linear pinning with the published pivot-coordinate torus at
`Fin.last n`. Its comparisons retain every rank, arbitrary characteristics and
universes. They do not assert the full special-linear Tits cocycle presentation.

`torusEntry_eq_lastPivot_torusWeights` identifies the finite torus's diagonal
entry with the pivot-coordinate product after reindexing. The proof changes
the finite product's index using `lastPivotEquiv` and uses the explicit weight
coordinate identity.

`lastPivotDiagonalTorus` constructs the actual group-scheme morphism from the
finite-coordinate split torus to the special-linear group by composing the
factor-renaming isomorphism with the published last-pivot diagonal inclusion.

`fin_diagonalTorus_eq_lastPivot` is equality of actual morphisms of group
schemes: the finite diagonal inclusion equals the factor-renaming isomorphism
followed by the pivot-coordinate diagonal inclusion. The proof compares points
on every relative test scheme, computes their matrices, and applies the entry
comparison. It places no affineness or field assumption on the test scheme and
works over any commutative base ring.

`fin_rootChar_eq_lastPivot` identifies each finite root character with the
pullback of the difference of its two diagonal-entry characters. It specializes
the integral-character pullback formula of `SpecialLinearTitsCocycleFinCoordinates`
to the finite root character's defining weight difference.

These are direct comparisons of the Library constructions in
`SpecialLinear.FinSucc` and `SpecialLinear`. Their provenance is internal:
finite-product reindexing, point formulas for actual torus morphisms, and the
character coordinate equivalence. No classification premise or new assertion
from external literature is used.
