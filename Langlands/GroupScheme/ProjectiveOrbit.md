# Actual projective orbit maps of finite matrix representations

Author: Worker 148.

This internal module derives actual projective orbit morphisms from the existing
finite matrix representation and relative projective coordinate action APIs.
It does not assert the existence of a representation with a prescribed stabilizer.

`coordinateEquiv` identifies invertible coordinate matrices with linear
equivalences. `matrixAction` applies their actual relative projective scheme
maps. Their composition law has the usual left-action order, and arbitrary
scheme restriction pulls back all matrix coefficients.

`pullbackPoint` pulls an actual map from the base to its relative projective
space to a section over any scheme test. Its definition uses the integral
projective-space projection, so it is a section even before a section law is
assumed for the initial map. Naturality follows from the two pullback projections.
`section_ext_of_map` shows that sections are determined after mapping to the
base's relative projective space. `translates_eq_iff` cancels the inverse matrix
action to identify equal translates with the right-difference fixed-point test.

`orbitSection` translates this chosen section by the representation's matrix
on an arbitrary scheme point. The point-matrix naturality and projective-action
naturality prove its compatibility with every test morphism. `ambient` is the
actual relative projective scheme over the coefficient spectrum; its structural
map is separated by comparison with polynomial projective space, which is proper.
`orbitMap` applies the universal point matrix on the group scheme itself and
then maps to this ambient scheme. `comp_orbitMap` identifies every pullback with
the corresponding matrix translate. Finally, `orbitMap_fibers` proves that two
group points have equal images exactly when their right difference fixes the
pulled-back section. These are equalities of actual scheme morphisms, including
their structure-sheaf maps, on all scheme tests.

A further comparison between fixed projective sections and scalar-unit
stabilizers of primitive coordinate vectors is still required to use the
Chevalley line-stabilizer criterion for subgroup quotient existence.
