# The local Weil transfer/inclusion square

Lean module: `Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof`
(namespace `Langlands.LocalClassField`).

Author: Worker 5078.

## Statement

`extensionWeilTransferReciprocity : ExtensionWeilTransferReciprocityStatement.{u, v}`
proves the published proposition exactly, at independent carrier universes `u`
and `v`. It quantifies over every prime `p`, every `F : PadicField.{u} p`,
`E : PadicField.{v} p`, every `f : F.Carrier →ₐ[Padic p] E.Carrier` and
arbitrary candidates `eF`, `eE` with `GeometricWeilReciprocityRelation`. It
adds no hypothesis. It is the transfer/inclusion square of Serre, *Local
Fields*, XI §3, diagram (2), in the formulation of the statement module.

## Helpers (namespace `ExtensionWeilTransfer`)

- `transfer_subgroupCongr`: Mathlib's transfer to `H` of `ϕ ∘ subgroupCongr`
  equals the transfer to `K` of `ϕ`, when `H = K` (by `subst`).
- `transfer_weilSubgroup`: for a common-closure family `eC` with
  `CommonClosure.TransferRelation`, every finite intermediate field `L`, and
  `y : W_F`, the transfer from `W_F` to `weilSubgroup F L` of
  `reciprocityUnits F eC L` at `y` is the bottom component
  `reciprocityUnits F eC (baseExtension F)` at `baseWeilEquiv F y`, followed by
  `unitsInclusion` from `⊥` to `L`.

  Proof. Let `ι` be the subtype map of the bottom subgroup `P_⊥` into `W_F`. It
  is surjective (`baseWeilEquiv F` gives preimages), so it has dense range.
  `TransferNaturality.transfer_comp_denseRange` moves the transfer from `W_F`
  to `P_⊥` along `ι`. The restricted map factors through the abelianization of
  `(weilSubgroup F L).comap ι`, so `GroupTheory.Transfer.transfer_comp` gives
  `eC L` of the abelianized transfer. This is, by unfolding,
  `eC L ∘ weilAbelianTransfer ⊥ L` at the projection of `baseWeilEquiv F y`.
  The transfer relation of `eC` for `⊥ ≤ L` turns it into the inclusion of the
  bottom component.

The bottom-field inclusion reuses `Langlands.LocalFactor.CommonClosure.baseExtension_le` from
`Langlands.Global.Factors.RelativeWeilLocalEpsilon`.

The module also declares two local instances: `CharZero F.Carrier` from
`Padic p`, and the topology `(fieldData F L).topology` on each finite
intermediate field, the one used by `reciprocityUnits`.

## Proof of the main theorem

1. `commonClosureReciprocityExistence` (module
   `CommonClosureExistenceProof`) gives a family `eC` on all finite
   intermediate fields of `AlgebraicClosure F.Carrier` with
   `NormalizedSystemRelation` for `F.canonicalTopologicalData`. Its
   `TransferRelation` component is `heC.1.2.1`.
2. `commonClosureGeometricProof.{u, v}` shows that
   `Correspondence.baseReciprocityCandidate F eC`, which satisfies
   `IsBaseReciprocity` by `baseReciprocityCandidate_spec`, and
   `extensionReciprocityCandidate F E f eC` are geometric reciprocity maps of
   `F` and `E`. By `geometricWeilReciprocityUniqueness`,
   `eF = baseReciprocityCandidate F eC` and
   `eE = extensionReciprocityCandidate F E f eC`.
3. Let `L = extensionFiniteIntermediate F E f`. On the range of
   `extensionWeilMap F E f`, the map `R_E ∘ rangeInverse` equals
   `(extensionIntermediateUnitsEquiv F E f).symm ∘ reciprocityUnits F eC L ∘
   subgroupCongr`, where `subgroupCongr` comes from
   `extensionWeilRange_eq_fixing`. Both sides are evaluated through
   `extensionImageWeilEquiv` and `InductionAlong.apply_rangeInverse`.
4. `GroupTheory.Transfer.transfer_comp`, `transfer_subgroupCongr` and
   `transfer_weilSubgroup` rewrite the left side of the square to
   `(extensionIntermediateUnitsEquiv F E f).symm` of the inclusion of the bottom
   component at `baseWeilEquiv F y`.
5. After moving the units equivalence to the other side, the values are compared
   in `AlgebraicClosure F.Carrier`. `baseReciprocityCandidate_spec` identifies
   the bottom component, through `IntermediateField.botEquiv`, with
   `R_F y`. `extensionFieldEmbedding_comp` identifies the image of `f x` with
   `algebraMap F.Carrier _ x`. The `botEquiv` round trip
   (`AlgEquiv.symm_apply_apply`) closes the goal.

No reciprocity family, comparison or functoriality premise is assumed. The
statement module and its imported pairs are unchanged.

## Use

`Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionProof`
applies this theorem at `{u, u}` to the published reduction
`localInducedRestriction_of_extensionSquare`. The theorem is also exactly the
target of task `2b6541a9-9007-4cc5-9a23-f5785fce6d55`.
