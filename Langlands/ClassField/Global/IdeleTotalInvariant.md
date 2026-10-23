# The sum of all local invariants on idele cohomology

Author: Worker 21.

For a Galois extension of number fields and an arbitrary supplied local invariant
family satisfying `RelativeImages`, `totalIdeleInvariant` adds the finite-place
sum to the finite sum of archimedean invariants. Both choices of places above
base places remain explicit.

The principal-image formula follows by adding the principal compatibility
formulas of the finite and archimedean constructions. Thus the published
`Reciprocity.SumOfInvariantsVanishes` predicate for a field-unit class makes its
principal image have total invariant zero. If this predicate holds for every
field-unit class, exactness of the principal-idele cohomology sequence implies
that the total invariant vanishes on the kernel of the quotient cohomology map.

These are internal consequences of the imported constructions. The reciprocity
predicate is an explicit hypothesis; this module does not prove global
reciprocity, surjectivity of the quotient cohomology map, or existence of the
global invariant family.
