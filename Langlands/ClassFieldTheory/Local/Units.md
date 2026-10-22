# Multiplicative and unit objects for local class field theory

Worker 21 authored this construction module. It uses an arbitrary prime `p`,
an arbitrary-universe finite extension `F : Langlands.PadicField p`, and
specified `T : F.TopologicalData`. The multiplicative group is the existing
`F.Carrierˣ`. Install `T.topology` to obtain its standard Mathlib units topology;
`multiplicativeTopology` exposes that exact choice. The integer and residue
rings are the accepted `T.Integers` and `T.ResidueField`.

`valuationRing` is the same integer ring with Mathlib's valuation-subring
interface. `unitSubgroup` and `principalUnitSubgroup` reuse its existing
subgroups of `F.Carrierˣ`. `integerUnitsEquiv` identifies the first with
`T.Integersˣ`. `integerUnitsInclusion` is induced by the actual inclusion of
the integer ring into the field, and `integerUnitsInclusionContinuous` supplies
its continuity from the subtype and units topologies. `residueUnits` is induced
by the actual residue map. `principalUnitsEquiv` reuses Mathlib's identification
of principal units with its kernel.

For every natural number `n`, `TruncatedIntegers n` is the quotient by the
`n`th power of the actual maximal ideal. `truncatedReduction` and
`truncatedUnitsReduction` are the quotient ring map and its map on units.
`congruenceUnits n` is the latter's kernel inside `T.Integersˣ`; its image
under the canonical inclusion is `unitFiltration n` inside `F.Carrierˣ`.
For positive `n`, the condition is congruence to one modulo the maximal
ideal power. For `n = 0`, the quotient is the zero ring and the kernel is
the whole integer-unit group. Thus the indexing includes Serre's `U^0 = U`.
`truncatedUnitsReductionContinuous` supplies continuity for the quotient-ring
topology, by continuity of the quotient map and the map-on-units construction.

`UnitQuotient n` is the actual quotient group by that kernel.
`unitQuotientProjection` and `unitQuotientReduction` are the canonical
projection and induced reduction homomorphism. Its intrinsic kernel
containment certificate is supplied directly. With `T.topology` installed,
the quotient carries the ordinary quotient-group topology. This module
does not replace it by an asserted discrete topology or assume surjectivity
of reduction.
The continuous versions `unitQuotientProjectionContinuous` and
`unitQuotientReductionContinuous` prove the intrinsic continuity obligations:
the former is the quotient map and the latter factors the continuous reduction.

`orderHom` takes a nonzero field element, represented by a unit, to the
accepted normalized order in multiplicative notation for the additive
integers. Its homomorphism certificate follows from multiplication of the
accepted discrete valuation and the logarithm law for nonzero values.
`ValuationQuotient` and `valuationQuotientProjection` are the actual quotient
of `F.Carrierˣ` by `unitSubgroup` and its projection. An isomorphism of this
quotient with the integers, continuity of the order map, and the unit
filtration's topological properties are separate theorem obligations.
`valuationQuotientProjectionContinuous` does provide the continuous canonical
projection, using the genuine quotient topology.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67 (1979):
Chapter II, Section 1, printed pages 26-28, for the valuation topology and
integer ring; Chapter IV, Section 2, printed page 66 (retained PDF page 73),
for the filtration `U^0 = U`, `U^n = 1 + m^n` for `n >= 1`, and reduction of
units. Source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
file `C:/Central-Library/Serre--Local Fields--1979.pdf`.

The source defines these objects on the actual valuation ring. The Lean
implementation uses quotient kernels and their images under the inclusion;
this is an implementation of the same congruence condition. Serre's further
claims about closedness, neighborhood bases and quotient identifications
are not supplied as assumptions or claimed as proved in this module.
There is no Artin map or reciprocity-existence assertion in these definitions.

## Exact dependencies

- `Langlands.LocalField.Definitions`, artifact
  `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1.
- `Langlands.LocalField.Normalization.Definitions`, artifact
  `e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2`, version 1.
- Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
  Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The direct Mathlib interfaces are `Valuation.valuationSubring`,
`ValuationSubring.unitGroup`, `ValuationSubring.principalUnitGroup`,
`unitGroupMulEquiv`, `principalUnitGroupEquiv`, `Units.map`,
`Continuous.units_map`, `Ideal.Quotient.mk`, `QuotientGroup.mk'`,
`QuotientGroup.lift`, and `WithZero.log_mul`. All construction certificates
are discharged from these existing results. No arithmetic-normalization
statement is used as a proved dependency.

## Topic-hierarchy migration

Worker 63 relocated this pair from `Langlands.LocalClassField.Units` to
`Langlands.ClassFieldTheory.Local.Units` at Library base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 21 remains the
author of every mathematical declaration and construction certificate above.
Only imports were rewritten in the Lean source; all declaration text, including
universes, hypotheses, definitions, proofs and instance declarations, was retained.
The old path is a declaration-free re-export with its own paired documentation.

The full [module table and declaration-preservation ledger](Completion.md#topic-hierarchy-migration-ledger)
records this mechanical migration and its validation. Original source citations
and mathematical explanations are retained; their historical submission-status
remarks describe the original contribution, not this relocation's review status.
