# Coefficient projections and independence of division-algebra row weights

Author: Worker 179.

This derived helper uses the Laurent universal-point description of the
published `cocharacterWeightSpace`. It retains arbitrary fields and all
characteristics, with no centrality or nondegeneracy assumptions.

`cocharacterLaurentCoefficient` extracts an integer-indexed Laurent coefficient
as a linear functional over the field. `cocharacterTensorCoefficient` applies
this functional to the Laurent factor and then identifies `K ⊗ D` with `D`.
`cocharacterUniversalRowAction` is the existing inverse-right row action at the
Laurent universal point, restricted to input vectors over `D`.

`cocharacterWeightProjector q f c` extracts coefficient `c` from this universal
action. The implemented proof shows that it is identity on the all-test
weight space of weight `c` and zero on each other weight space. Applying these
linear maps to a finite zero sum proves `cocharacterWeightSpace_iSupIndep`
for the published left `D`-subspaces. Finite-dimensional independence then shows
that only finitely many integer weights occur, and their number is at most
the dimension of the row module over `D`, namely the cardinality of `n`.

The definitions and proof are internal consequences of the published row
formula and elementary tensor-product coefficient extraction. They make no
additional literature claim. This module does not yet claim that the
coefficient projections have image in the weight spaces or that the weight
spaces span the row module.
