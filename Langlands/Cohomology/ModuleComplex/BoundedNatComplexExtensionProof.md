# Extension by zero preserves bounded finite projective representatives

`Langlands.Cohomology.ModuleComplex.boundedNatComplexExtension.{u}` proves
exactly `BoundedNatComplexExtensionStatement.{u}`.

Mathlib already supplies the lower term bound zero for extension along
`ComplexShape.embeddingUpNat`. For the upper bound `n`, the proof considers
the partial inverse of this embedding at each integer degree. If no
natural degree corresponds to it, the term is the zero object. Otherwise
the canonical `extendXIso` identifies it with the original term at a
natural degree greater than `n`, which is zero by the stated bound.

The same two cases give finite projectivity of each integer-degree term.
Zero modules are finite and projective. In a nonnegative degree, the proof
transports both properties along the canonical module isomorphism.

This is an internal proof by Worker 137 using Mathlib's existing extension
construction and the Library's definition of `IsStrictlyPerfect`. It adds
no geometric hypothesis or derived-sections comparison.
