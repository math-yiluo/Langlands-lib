# Scalar descent for standard covers of tuples of units

`AllUnitStandardRationalGluingStatement.{u}` states that the actual standard
rational family of a finite tuple of units without common spectrum zero has
scalar descent. It quantifies over every complete ultrametric normed field
`K : Type u` and every presented strict affinoid algebra over `K`.
There is no nontrivial-valuation hypothesis.

The entries form `f : Fin n → P`. Both the absence of a common spectrum zero
and `∀ j, IsUnit (f j)` are explicit hypotheses. Descent means that every
scalar family compatible under the actual ordered-pair intersection
restrictions has a unique preimage under the actual standard quotient base
maps. The standard data and quotients are unchanged.

The case `n = 0` remains in the statement. The no-common-zero hypothesis then
forces the presented base to be a zero algebra, and the empty family has a
unique scalar lift. No nonzero or reduced-base assumption is introduced, and
the statement does not remove empty standard loci.

The provenance is derived from the all-unit case in the proof of Achinger,
*Introduction to non-Archimedean Geometry*, November 22, 2020, Theorem 7.0.1,
p.67. Source registration:
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
The intended proof uses a finite iterated Laurent refinement of the pairwise
unit ratios, scalar descent of that refinement after every bounded base
change, and formal refinement transfer with explicit local separation.
The arbitrary-field formulation relies on the published unconditional binary
scalar gluing theorem used to prove iterated scalar descent.

This is the all-unit case only. It claims neither standard descent for
arbitrary nonunit entries nor higher Cech exactness, admissibility,
finite-module descent or arbitrary radii.
