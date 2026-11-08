# Naturality of compact induction normalization and subgroup transport

This internal construction combines an existing representation equivalence
to compact induction with an ambient smooth scalar character, equality of
the inducing subgroups and an equivalence of coefficients. It acts on the
actual compact functions through the character twist, subgroup equality
and coefficient postcomposition.

`subgroupCongr` and `subgroupTransport` are the shared forms of the identical
private helpers formerly in `RepresentedGeometricLemmaCompactInduction`.
That module now uses these definitions with the same types and bodies.

The naturality theorem assumes naturality of the existing equivalences
and of the coefficient equivalences for three given intertwiners. Its proof
eliminates the subgroup equality, compares actual function values, uses the
first naturality identity and commutes scalar multiplication through the
coefficient maps to apply the second identity. These are generic derived
transport facts; no geometric comparison or structural existence is assumed.
