# Compatibility of the relative and absolute invariant maps

Author: Worker 42.

`InvariantFamily.ClosureCompatibility` is a predicate on the law-free
candidate invariant family. For every finite Galois intermediate field
`E` of the actual algebraic closure of a p-adic field `F`, and every
class `x` in the continuous cohomology of `Gal(E/F)` with its discrete
unit coefficients, it asserts the equation

`inv_F(closureContinuousInflation x) = inv_(E/F)(continuousToRelative x)`.

Both maps in this equation have already been constructed from actual
cochain maps in `ClosureCoefficients`. The left side uses continuous
inflation through restriction of actual algebraic-closure automorphisms
and inclusion of actual units. The right side uses the published
continuous-to-ordinary comparison for the unchanged unit action.
The equation does not identify finite relative cohomology with
continuous absolute cohomology.

For a finite group with discrete topology the forward comparison is
expected to be invertible, but that is a separate obligation of the
generic continuous-comparison task. This predicate does not assume an
inverse or choose one from an unproved assertion. Consequently it is
already a precise compatibility diagram on continuous representatives;
using it to define a map on every ordinary class still requires the
separate comparison theorem. Neither this predicate nor the coefficient
constructions claim an invariant existence theorem.

The base and the actual intermediate fields of its closure lie in
arbitrary `Type u`. This clause uses `InvariantFamily.{u,u}` because
it concerns subfields of this one closure. It performs no resizing of
an independently presented finite extension in a different universe;
the independent-universe relative-image and normalization predicates
remain in `Invariants`.

The original source is Jean-Pierre Serre, *Local Fields*, English
translation by Marvin Jay Greenberg, Springer GTM 67 (1979), Chapter X,
Section 3, printed pages 154–155 (PDF pages 160–161), for the finite-stage
description of continuous Galois cohomology, and Chapter XIII, Section 3,
Propositions 6–7, printed pages 193–194 (PDF pages 198–199), for the local
invariant and its restriction to relative groups. The displayed commuting
diagram is the implementation of that compatibility through the two
existing cochain models.

Source ID: `serre-1979-local-fields`; retained original
`C:/Central-Library/Serre--Local Fields--1979.pdf`; SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The arithmetic sign is inherited from `InvariantFamily.ArithmeticNormalization`
and its positive carry class. This compatibility equation introduces
no additional sign. Corestriction and the complete simultaneous local
realization remain separate clauses to be assembled using genuine maps.
