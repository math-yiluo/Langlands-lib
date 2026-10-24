# The full logarithmic unit lattice

For a number field `E : Type v`, `fullLogUnitLattice E` is an integral
submodule of the real sum-zero hyperplane `fullLogHyperplane E`. It is the
pullback of Mathlib's `NumberField.Units.unitLattice E` through the real
linear equivalence `fullLogHyperplaneEquiv E`. Thus it uses all the actual
infinite places, with the logarithmic normalization fixed in `FullLogEmbedding`.
There is no Galois or cyclicity hypothesis.

`mem_fullLogUnitLattice` identifies membership with the existence of an actual
unit `x : Additive (𝓞 E)ˣ` whose full logarithm into the hyperplane equals the
given vector. Its proof unfolds membership in Mathlib's image submodule, uses
`fullLogHyperplaneEquiv_log`, and applies injectivity of the coordinate
equivalence. `fullLogUnitLattice_eq_range` expresses the same result as equality
with the range of the integer linear map associated to
`fullLogEmbeddingToHyperplane E`.

`instDiscreteTopologyFullLogUnitLattice` and
`instIsZLatticeFullLogUnitLattice` transport Mathlib's discrete full unit lattice
through the continuous linear equivalence associated to
`fullLogHyperplaneEquiv E`. Continuity follows from finite dimensionality of
the real coordinate spaces. The instances use the standard subspace topology
on the hyperplane and on the lattice. In particular,
`fullLogUnitLattice_span` proves that its real span is the whole hyperplane.
These conclusions include the case of a field with only one infinite place,
when the hyperplane and lattice are zero.

`fullLogEmbeddingEquiv E` is an integer linear equivalence

```
Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E) ≃ₗ[ℤ] fullLogUnitLattice E.
```

It composes Mathlib's `NumberField.Units.logEmbeddingEquiv E` with
`ZLattice.comap_equiv` for the full-coordinate equivalence. The local additive
group instance is the existing quotient-group instance through `Additive`;
it introduces no new group operation. `fullLogEmbeddingEquiv_apply` proves
that the class of every actual unit maps to its full logarithm in the
hyperplane. The proof reduces the composite to the inverse coordinate
equivalence, then uses `fullLogHyperplaneEquiv_log` and the inverse identity.

The source is J. S. Milne, *Class Field Theory*, v4.03 (2020), Chapter VII,
proof of Proposition 3.1, printed p.209 (PDF p.218). With the set of places
specialized to all infinite places, the source's image `M₀` of the unit
logarithm is a full lattice in the sum-zero subspace `V₀`, with roots of unity
as kernel. This module establishes that specialization by transporting
Mathlib's Dirichlet unit theorem; it does not formalize the general theorem
for units outside a finite set of places. The pullback construction and its
exact comparison to Mathlib are internal adapters.

The implementation reuses the pinned Mathlib modules
`Mathlib.NumberTheory.NumberField.Units.DirichletTheorem` and
`Mathlib.Algebra.Module.ZLattice.Basic`, specifically `unitLattice`, its
`DiscreteTopology` and `IsZLattice` instances, `logEmbeddingEquiv`,
`ZLattice.comap`, and `ZLattice.comap_equiv`. The imported `FullLogEmbedding`
provides the full-coordinate equivalence and its logarithm comparison.
This prerequisite proves the lattice and quotient identification. Galois
stability and equivariance, enlargement by a constant vector, and the
cohomological Herbrand formulas remain separate obligations.
