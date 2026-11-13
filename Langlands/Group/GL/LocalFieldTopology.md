# Topological certificates over an arbitrary nonarchimedean local field

Author: Worker 5089.

This helper module proves topological properties of a nonarchimedean local field, its
unit group, the general linear group `GeneralLinear n F` and its upper unipotent
subgroup. The field context is the one used throughout the all-field statements:

```lean
variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
```

with every characteristic allowed. The p-adic files obtain these properties from
`PadicField.TopologicalData`; here they are derived from Mathlib's
`IsNonarchimedeanLocalField` instead. Every declaration is a theorem with explicit
arguments `F` (and `n`), not a global instance, so importing the module changes no
instance search. Downstream modules install the ones they need with
`attribute [local instance]`.

## Declarations

All are in the namespace `Langlands.LocalFieldTopology`.

| Theorem | Conclusion |
| --- | --- |
| `t2Space F` | `T2Space F` |
| `secondCountableTopology F` | `SecondCountableTopology F` |
| `totallyDisconnectedSpace F` | `TotallyDisconnectedSpace F` |
| `units_locallyCompactSpace F` | `LocallyCompactSpace Fˣ` |
| `units_totallyDisconnectedSpace F` | `TotallyDisconnectedSpace Fˣ` |
| `generalLinear_t2Space F n` | `T2Space (GeneralLinear n F)` |
| `generalLinear_locallyCompactSpace F n` | `LocallyCompactSpace (GeneralLinear n F)` |
| `generalLinear_secondCountableTopology F n` | `SecondCountableTopology (GeneralLinear n F)` |
| `generalLinear_sigmaCompactSpace F n` | `SigmaCompactSpace (GeneralLinear n F)` |
| `generalLinear_nonarchimedean F n` | `NonarchimedeanGroup (GeneralLinear n F)` |
| `generalLinear_totallyDisconnectedSpace F n` | `TotallyDisconnectedSpace (GeneralLinear n F)` |
| `generalLinear_compactOpen F n U hU` | every identity neighborhood `U` of `GeneralLinear n F` contains a compact open subgroup |
| `upperUnipotent_t2Space F n` | `T2Space (GeneralLinear.upperUnipotent n F)` |
| `upperUnipotent_locallyCompactSpace F n` | `LocallyCompactSpace (GeneralLinear.upperUnipotent n F)` |
| `upperUnipotent_secondCountableTopology F n` | `SecondCountableTopology (GeneralLinear.upperUnipotent n F)` |
| `upperUnipotent_nonarchimedean F n` | `NonarchimedeanGroup (GeneralLinear.upperUnipotent n F)` |

The private definition `rankOne` is a `Valued.v.RankOne` structure used inside the
proofs only.

## Proofs

**The field.** The proofs give `F` the right uniform structure of its additive
topological group (`IsTopologicalAddGroup.rightUniformSpace`). Mathlib's
`IsNonarchimedeanLocalField` then supplies the `Valued` instance, and Hausdorffness
follows by instance search. For second countability and total disconnectedness the
private `rankOne` makes the valuation rank one. It composes the order embedding of
the value group given by `ValuativeRel.IsRankLeOne` with
`MonoidWithZeroHom.ValueGroup₀.embedding`, and strict monotonicity comes from the same
two maps. With `open scoped Valued`, this gives `F` its valued normed field structure.
A nontrivially normed field that is weakly locally compact is proper
(`ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`), so it is second
countable. Its norm is ultrametric, so it is totally disconnected. Both conclusions
concern only the given topology of `F`, which the uniform and normed structures above
induce.

**Units.** `Units.val : Fˣ → F` is an embedding for the topology of `Fˣ` as a
group with zero (`Units.isEmbedding_val₀`), with open range `{0}ᶜ`, because `F` is
Hausdorff. An open embedding into a locally compact space gives local compactness, and
the embedding transports total disconnectedness.

**`GeneralLinear n F`.** The matrix space `Matrix (Fin n) (Fin n) F` has the product
topology of `Fin n → Fin n → F`, so it inherits Hausdorffness, local compactness,
second countability and total disconnectedness from `F`. Mathlib's instances for unit
groups give Hausdorffness and local compactness of `GeneralLinear n F`. Second
countability comes through the inducing map `Units.embedProduct` into
`Matrix × Matrixᵐᵒᵖ`. Sigma-compactness follows from second countability and local
compactness. The published `valuativeGeneralLinearNonarchimedean F n` (in
`Langlands.Group.GL.Nonarchimedean`) gives `NonarchimedeanGroup`. Total
disconnectedness comes from the injective continuous map `Units.val` into the totally
disconnected matrix space. `generalLinear_compactOpen` is the Library's
`compactOpenSubgroupBasis` (from `Langlands.Topology.CompactOpen.NeighborhoodBasis`)
applied with these instances.

**Upper unipotent subgroup.** Hausdorffness is inherited by the subtype.
Local compactness is the Library's `GeneralLinear.UpperUnipotent.locallyCompactSpace`.
Second countability follows from the subtype embedding. The nonarchimedean property
is shown directly: an identity neighborhood of the subgroup is the preimage of an
identity neighborhood `W` of `GeneralLinear n F`. `W` contains an open subgroup `L`,
whose comap along the subtype inclusion is an open subgroup of the unipotent group
inside the given neighborhood.

## Provenance

These are standard topological facts, internal to this project; no source text is
transcribed. They replace, for an arbitrary nonarchimedean local field, the p-adic
certificates of `PadicField.TopologicalData` (for example
`generalLinearLocallyCompactSpace`, `generalLinearSigmaCompactSpace`,
`generalLinearT2Space`, `generalLinearNonarchimedean`) used in the p-adic
multiplicity-one proof. The module supports
`Langlands.Representation.Whittaker.LocalFieldShalikaInvariance`,
`Langlands.Representation.Smooth.Contragredient.LocalFieldGelfandKazhdan` and
`Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof`.
