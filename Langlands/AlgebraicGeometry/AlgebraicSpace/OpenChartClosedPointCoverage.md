# Covering an atlas by checking closed points

This internal module combines the preceding open-subfunctor membership and
atlas-coverage helpers with the Jacobson property of schemes locally of finite
type over an arbitrary field. It adds no algebraic-geometric assumption to the
existing atlas argument except local finite type of the atlas scheme over the
field. Neither quasi-compactness nor perfectness of the field is required.

`OpenSubfunctorPoints.mem_residueField_iff_mem_range` identifies membership of
the residue-field value of a section in an open subfunctor with membership of
the underlying point in the topological image of the represented open
pullback. The proof applies the existing range-containment criterion, using
that the canonical residue-field morphism has constant value equal to that
point.

`mem_residueField_of_specializes` then transfers this membership from a
specialization to a generization: the represented pullback has open image,
and open subsets are stable under generization. Consequently
`mem_iff_closed_residueField` tests membership of a section on a locally finite
type scheme over a field using only its closed-point values. Every point has
a closed specialization by `FieldSchemePoints.exists_closed_specialization`.

`OpenChartCoverage.residueField_coverage_of_closed` applies this argument to
the range subfunctor of each chart. Given an arbitrary atlas point, choose a
closed specialization, a chart containing its residue-field value, and then
transfer membership back to the original point. The chart index can depend
on the chosen closed specialization.

`isLocallySurjective_sigma_of_closed_residueField` composes this reduction
with `isLocallySurjective_sigma_of_residueField`. Its conclusion is the
local surjectivity of the coproduct of the open charts for the fppf topology,
as required by the open-chart gluing statement. These are derived internal
results; their provenance is the imported helper modules and Mathlib's
topological specialization theorem.
