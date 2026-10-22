# Canonical residue and valuation transport to the image field

Author: Worker 20. This is an internal specialization of the arithmetic transport
construction in [CanonicalTransport](../../LocalField/CanonicalTransport.md).
All declarations here lie in `Langlands.LocalClassField`.

## Inputs and exact image field

Fix a prime `p`, `F : PadicField.{u} p`, `E : PadicField.{v} p`, and an actual
algebra homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`. The universes are
independent. Write `J = extensionFiniteIntermediate F E f`. Its field is the
actual image of the already chosen algebraic-closure embedding; its topological
and arithmetic data are exactly `CommonClosure.canonicalData F J`.

The field equivalence is the published `extensionIntermediatePadicEquiv F E f`
from `E` to `J.asPadicField`. The latter uses the specified composite p-adic
algebra structure. The proofs install precisely that structure, with no new
embedding, valuation or reciprocity choices.

## Constructions and identities

`extensionIntermediateResidueEquiv` specializes `CanonicalTransport.residueEquiv`
to this field equivalence. It identifies `E.canonicalTopologicalData.ResidueField`
with `(CommonClosure.canonicalData F J).ResidueField` by the actual induced
residue maps. It is a ring equivalence, not merely an equality of dimensions.

`extensionIntermediate_residueCardinality` applies `Nat.card_congr` to it and
proves exactly

```
(CommonClosure.canonicalData F J).residueCardinality =
  E.canonicalTopologicalData.residueCardinality.
```

`extensionIntermediate_ord` and `extensionIntermediate_discreteValuation`
specialize the two arithmetic preservation theorems to
`extensionIntermediatePadicEquiv F E f x`, for every `x : E.Carrier`.
Both statements include zero. The order convention there remains zero, and
the discrete valuation there remains zero in its multiplicative value group.

`extensionIntermediateUnitsEquiv_discreteValuation` states the same valuation
identity for the existing topological multiplicative equivalence on units.
Its underlying field map is definitionally the above algebra equivalence, so
the proof directly applies `extensionIntermediate_discreteValuation`.
The statement explicitly installs both canonical topologies as required by
the existing units construction.

## Derived provenance and scope

The direct imports are `Langlands.ClassFieldTheory.Local.ExtensionFieldTransport`
and `Langlands.LocalField.CanonicalTransport`. The first supplies
`extensionFiniteIntermediate`, `extensionIntermediatePadicEquiv`, and
`extensionIntermediateUnitsEquiv` on the exact image field; its paired
Markdown explains their construction. The second supplies the actual residue
equivalence and arithmetic preservation with their implemented proofs.
There is no new assertion from original literature in this specialization.

The cardinality identity permits downstream comparison at the identical
spectral coordinate `q_E^(-s)`. The valuation identities permit downstream
comparison of actual filtration levels and conductor predicates. Those
factor/conductor comparisons are not asserted by this module. Neither chosen
uniformizer equality nor arbitrary designated-extension identification is
claimed. The existing choice of closure embedding is retained; its independence
and coherence, reciprocity existence and epsilon-system existence remain
separate obligations.
