# The algebraic boundary of the actual rational dynamic open cell

Author: Worker 135.

`Langlands.Plancherel.RationalDynamicOpenCellBoundaryStatement.{u}` is a
proposition for every field `F` in arbitrary universe, every actual
smooth affine group scheme `G` over `Spec F`, and every cocharacter
`chi` defined over `F`. It has no topological-field, reductivity,
connectedness, splitness, or characteristic premise.

The statement uses the same actual identity-test rational points,
dynamic parabolic `P`, opposite dynamic unipotent subgroup `V`, and
map `(p, v) ↦ p * v⁻¹` as `RationalDynamicOpenCellConullStatement`.
It requires a proper Zariski-closed subset `Z` of the underlying actual
scheme of `G` whose inverse image under rational-point evaluation
`p ↦ p.left (IsLocalRing.closedPoint F)` is exactly the complement of
that map's range. Proper means `Z ≠ Set.univ`; the boundary is allowed
to be empty.

This is an internal geometric prerequisite for the conullness proof.
The intended argument uses the published actual opposite multiplication
cell from `GroupScheme.Absolute.OppositeCellProof`, composes that open
immersion with scheme inversion, and identifies its rational points
with the range of the prescribed map. A rational point lands in an
open immersion's image exactly when it lifts through that immersion:
the field spectrum has a unique point, and the scheme lift respects
the given base morphism. No external source assertion is claimed for
this extracted comparison.

This file defines a statement only. It asserts neither Haar nullness
of the boundary nor its inverse image, and it is not a proof of the
host conullness target. Local density, measure regularity, and the
Haar-null closed-set theorem remain separate obligations. The analytic
open embedding of the same actual map is already proved in
`HarishChandraSchwartz.OpenCellPoints`.
