# Full central quotients of product groups

Author: Worker 190.

This module constructs the continuous group equivalence

```text
(∏ i, G i) / Z(∏ i, G i) ≃ₜ* ∏ i, (G i / Z(G i))
```

for a dependent family of topological groups. Here `Z` is Mathlib's full
`Subgroup.center`. Both quotient spaces carry the existing quotient topologies,
and both products carry the existing product topologies. The center itself has
its subgroup subtype topology. No topology is replaced or transported.

The index type is `ι : Type uI` and the family is `G : ι → Type uG`, with
independent universes. The construction works for arbitrary index types and
therefore supplies the requested finite-product construction, including an empty
index type. It requires no chosen coordinate, `Nonempty ι`, Hausdorff assumption,
local compactness, or countability. Classical choice is used to choose quotient
representatives, so the quotient equivalences are noncomputable.

## Public interface

All declarations below are in `Langlands.Group.Center`. The explicit parameter
`G` denotes the family; group, topology, and topological-group structures are
inferred instances.

| Declaration | Meaning |
| --- | --- |
| `mem_center_pi_iff G g` | A tuple is central exactly when all its coordinates are central. |
| `quotientPi G` | The homomorphism `g ↦ (i ↦ [g i])` from the product group to the product of full central quotients. |
| `ker_quotientPi G` | Its kernel equals the full center of the product group. |
| `quotientPi_surjective G` | Every tuple of quotient classes has a tuple of representatives. |
| `quotientPiMulEquiv G` | The induced algebraic group equivalence from the central quotient of the product. |
| `piCenterContinuousMulEquiv G` | The continuous group equivalence `Z(∏ i, G i) ≃ₜ* ∏ i, Z(G i)`. |
| `quotientPiContinuousMulEquiv G` | The main continuous group equivalence on actual central quotients. |
| `quotientPiMeasurableEquiv G` | The same equivalence on any Borel realizations of its domain and codomain. |

The algebraic declarations require only `[∀ i, Group (G i)]`.
`piCenterContinuousMulEquiv` additionally requires
`[∀ i, TopologicalSpace (G i)]`; its continuity uses only subtype and product
topologies. The main quotient continuous equivalence also requires
`[∀ i, IsTopologicalGroup (G i)]`.

The representative formulas, each marked `simp`, are

```text
quotientPiMulEquiv_mk G g
quotientPiContinuousMulEquiv_mk G g
quotientPiMeasurableEquiv_mk G g
```

They assert that each equivalence maps `QuotientGroup.mk g` to
`fun i => QuotientGroup.mk (g i)`. The respective `_symm_mk` lemmas assert that
its inverse maps this tuple of classes to `QuotientGroup.mk g`. Thus the inverse
formula applies to any choice of coordinate representatives, independent of the
choice used to construct the inverse.

`piCenterContinuousMulEquiv_apply` says that the underlying value of coordinate
`i` is `z.1 i`, and `piCenterContinuousMulEquiv_symm_apply` says that coordinate
`i` of the inverse is the underlying value of `z i`.

The bundled `continuous_toFun` and `continuous_invFun` fields of
`quotientPiContinuousMulEquiv G` give continuity in both directions, and its
`toHomeomorph` gives the homeomorphism directly. The explicit measurability
lemmas are `measurable_quotientPiContinuousMulEquiv` and
`measurable_quotientPiContinuousMulEquiv_symm`.

## Implemented construction and intrinsic proofs

`Subgroup.center_pi` identifies the full center as the subgroup of tuples in
all the coordinate centers. Simplifying membership gives
`mem_center_pi_iff`. The center equivalence then packages the same coordinates
as subtypes in either direction. Its inverse and multiplicativity laws are
coordinatewise reflexivity, and continuity follows from the continuous product
projections and subtype-value maps.

For the quotient construction, define the coordinate homomorphism
`quotientPi`. The quotient criterion `QuotientGroup.eq_one_iff` proves that its
kernel is precisely the full center. Coordinatewise surjectivity of the
quotient maps and classical choice prove surjectivity of `quotientPi`.
`QuotientGroup.liftEquiv` then supplies `quotientPiMulEquiv`. Its forward
representative formula is definitional, and its inverse representative formula
is the equivalence's inverse law.

The composite of the forward equivalence with the product group's quotient map
is `quotientPi`, which is continuous coordinatewise. The quotient-map universal
property therefore proves continuity of the forward equivalence. In the reverse
direction, each coordinate quotient map is an open quotient map by
`QuotientGroup.isOpenQuotientMap_mk`. Mathlib's
`IsOpenQuotientMap.piMap` proves the product map is an open quotient map even for
an arbitrary index type. Composing the inverse equivalence with this product
map gives the quotient map of the product group, by the inverse representative
formula. The open quotient-map universal property proves inverse continuity.

The measurable equivalence is exactly
`(quotientPiContinuousMulEquiv G).toHomeomorph.toMeasurableEquiv`; its
measurability assertions follow from continuity.

## Borel hypotheses and downstream scope

The Borel section explicitly assumes `MeasurableSpace` and `BorelSpace` on the
entire central quotient of the product and on the entire product of central
quotients. It does not identify the Borel sigma-algebra of an arbitrary product
with the product of coordinate sigma-algebras. Consumers using product measures
must supply that Borel compatibility for their product measurable space. For
countable indices and second-countable Borel coordinate spaces, Mathlib's
`Pi.borelSpace` supplies it; this includes the relevant finite products once the
coordinate quotient topology properties are installed. One may also directly
choose the Borel sigma-algebra of the entire product for these adapters.

This is quotient geometry only. It does not transport Haar measures, establish
Haar uniqueness, compare `MemLp`, factor matrix coefficients, or prove any of
the analytic block-tensor statements. It does not identify the product center
with the scalar center of an ambient general linear group. It imports only
Mathlib, so the existing `BlockTensorAnalyticStatement` pair and all its imports
remain unchanged.

## Provenance

This is an internal construction from the definitions of products, full group
centers, and quotient groups, with the intrinsic proofs described above. It is
not attributed verbatim to an external literature theorem and needs no
representation-theoretic or analytic premise. Its Mathlib inputs are the center
identity, the quotient universal property and first-isomorphism construction,
product/subtype topology results, openness of group quotient maps, and the
Borel adapter for homeomorphisms, all from the project's pinned environment.
