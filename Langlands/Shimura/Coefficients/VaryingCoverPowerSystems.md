# Coefficient-power systems of associated sheaf diagrams

Author: Worker 13.

This internal construction composes
[VaryingCoverInverse](VaryingCoverInverse.md) with the genuine quotient
diagrams and canonical comparisons in
[VaryingCoverReduction](VaryingCoverReduction.md) and
[Reduction](Reduction.md).

Let `R` be a commutative ring, `I` an ideal of `R`, `X` a scheme,
`D : J ⥤ GrpCat` a group diagram, and `Y : EquivariantDiagram D X.Etale`.
Every `Y.action j` must satisfy the actual `IsFiniteGeometricTorsor`
predicate. A coefficient input is a varying-group equivariant diagram
`M : EquivariantDiagram D (ModuleCat R)`. Scheme, ring, group and module
carriers share universe `u`; the cover-index object and morphism universes
`uJ` and `vJ` are independent.

Write `A(M)` for the actual varying-cover associated-sheaf diagram,
`P_n(M)` for the coefficient diagram obtained by quotienting each module
by `I^n • ⊤`, and `Q_n` for sectionwise module reduction followed by
sheafification. The power index is `ℕᵒᵖ`, includes zero, and is independent
of the cover index `J`.

`etaleAssociatedCoefficientPowerSystems` is the functor
`M ↦ (n ↦ A(P_n(M)))`. Its cover transitions are the genuine
coefficient-diagram transition maps followed by inverses of the proved torsor
comparisons, applied to the reduced coefficient diagram. Its power
transitions and maps of input diagrams are images of the actual module
quotient transitions and coefficient morphisms.

`etaleAssociatedSheafPowerSystems` is `M ↦ (n ↦ A(M) ⋙ Q_n)`.
Its cover transitions are `Q_n` applied to those of `A(M)`.
Power transitions are the existing sheaf quotient transitions, applied
at every cover index. Both constructions are functors to
`ℕᵒᵖ ⥤ (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat R))`;
their functor laws are inherited from the composed functors.

`etaleAssociatedVaryingPowerUnit_app` identifies, at each cover index,
the composite of the sheaf quotient unit and the canonical comparison
with the component of `A(coefficientDiagramPowerUnit)`. It is the
existing comparison-unit equation expressed using the actual diagram
functor. Its reassociated form is also available.

`etaleAssociatedVaryingPowerComparison` has component at `j`
equal to the existing `constantAssociatedPowerReductionComparison`
from `Q_n A(M)_j` to `A(P_n(M))_j`.
Its naturality across a cover arrow is proved by cancellation against
the genuine sheaf quotient unit, which is an epimorphism. Naturality
of that quotient unit moves the original cover transition past it.
The existing comparison-unit equation then identifies both composites
with components of the associated-diagram morphism induced by
`coefficientDiagramPowerUnit`. Naturality of that actual morphism
proves the required square. No new coherence of inverses is assumed.

`etaleAssociatedVaryingReductionSystemsComparison` assembles the
comparisons into a natural transformation between the two functors.
Naturality in powers is the existing comparison-transition equation
at each cover index; naturality in input diagrams is the existing
coefficient naturality. The comparison-unit theorem identifies its
composite with the sheaf quotient units as the associated-diagram map
induced by the genuine coefficient-diagram quotient unit. The final
formulas state the objects and the exact component of the comparison.

The provenance is this categorical assembly of published constructions,
with the new cover-naturality obligation proved as described. No new
external-source claim is made. These are ordinary module-sheaf diagrams
and canonical morphisms; no comparison is asserted to be invertible.
The unit does not construct Harris-specific torsors, diagonalize the two
indices, take inverse limits, prove smoothness or scalar extension, or
identify cohomology. Those remain separate constructions or theorems.
