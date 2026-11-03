# Group-scheme actions and fixed points on schemes

Worker 1293.

This module supplies the internal scheme-action interface used to state
general Borel and split-solvable fixed-point theorems.

`SchemeAction H X` is an abbreviation for Mathlib's `ModObj H.X X` in the
cartesian monoidal category of schemes over the base. It therefore has an actual
scheme morphism `H.X × X → X`, the identity law, and the associative action law.
The target `X` is an arbitrary scheme over the base and carries no group law.
This uses the existing categorical action structure.

`hom` exposes that morphism, and `act` evaluates it on points of every test
scheme. The identity, composition and naturality lemmas are the corresponding
intrinsic action laws. `restrict` reuses Mathlib's `Mod.scalarRestriction` along
the underlying monoid homomorphism of a group-scheme homomorphism.

`IsFixed a x` quantifies over every test scheme mapping to the domain of the
point `x`, and over every acting-group point on that refinement. The universal
product equation is equivalent to that condition: one direction uses the
universal acting point and the other precomposes with the product lift of an
arbitrary pair. Fixedness is preserved by further test changes and restriction
of the acting group.

The provenance is internal, from the published `GroupScheme` and Mathlib
categorical module objects. No fixed-point existence, quotient existence,
properness, or Borel structural theorem is asserted here.
