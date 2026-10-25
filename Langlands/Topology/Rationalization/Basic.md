# The final topology on a rational tensor product

Module `Langlands.Topology.Rationalization.Basic`, namespace
`Langlands.Topology.Rationalization`.

## Setting

Let `M` be an additive commutative group with a topology. No compatibility of
the topology with the group law is assumed (no `IsTopologicalAddGroup`), and no
compactness or separation hypothesis is made. The carrier is Mathlib's actual
tensor product `ℚ ⊗[ℤ] M` of `ℤ`-modules; nothing in this module replaces it by
a type synonym or a localization. For each rational number `q` there is the
additive map

```
x ↦ q ⊗ₜ[ℤ] x : M → ℚ ⊗[ℤ] M,
```

called the `q`-th tensor chart below.

## The topology

`finalTopology M : TopologicalSpace (ℚ ⊗[ℤ] M)` is the final topology for the
family of all tensor charts: a subset `U` of `ℚ ⊗[ℤ] M` is open exactly when,
for every `q : ℚ`, its preimage `{x : M | q ⊗ₜ[ℤ] x ∈ U}` is open in `M`. The
definition uses Mathlib's `TopologicalSpace` constructor directly with this
predicate. The three axioms hold because preimages commute with intersections
and unions: `univ` pulls back to `univ`, the preimage of `U ∩ V` is the
intersection of the preimages, and the preimage of a union of a family of
subsets is the union of their preimages.

`finalTopology` is a `def`, not an instance: this module installs no global or
scoped topology on `ℚ ⊗[ℤ] M`. Users install it locally with
`letI := finalTopology M`, or write `Continuous[finalTopology M, finalTopology N]`
(`open Topology`). Like Mathlib's `TopologicalSpace.coinduced`, the definition
carries the attribute `@[instance_reducible]`, which lets instance resolution
unfold it after local installation.

## Declarations

All declarations below lie in the namespace
`Langlands.Topology.Rationalization`. Throughout, `M : Type u` and
`N : Type w` carry only `[AddCommGroup _] [TopologicalSpace _]`, and the target
`X : Type v` of the criterion carries only a topology `t`. The universes `u`,
`v` and `w` are independent.

- `isOpen_finalTopology_iff`: for `U : Set (ℚ ⊗[ℤ] M)`,
  `IsOpen[finalTopology M] U ↔ ∀ q : ℚ, IsOpen ((fun x : M => q ⊗ₜ[ℤ] x) ⁻¹' U)`.
  This is the defining property and holds by `Iff.rfl`.
- `isClosed_finalTopology_iff`: the same statement for closed sets, since
  complements commute with preimages.
- `finalTopology_eq_iSup_coinduced`:
  `finalTopology M = ⨆ q : ℚ, TopologicalSpace.coinduced (fun x : M => q ⊗ₜ[ℤ] x) ‹_›`.
  Mathlib orders topologies so that `t₁ ≤ t₂` means that `t₁` is finer, that
  is, it has at least the open sets of `t₂`. In this order a supremum has as
  open sets exactly the sets open in every member (`isOpen_iSup_iff`), and the
  coinduced topology of a map has as open sets those whose preimage is open
  (`isOpen_coinduced`). The final topology of a family is therefore a supremum
  in Mathlib's order. In the order by inclusion of open sets the same topology
  is an infimum. The proof compares open sets with `TopologicalSpace.ext_iff`.
- `continuous_finalTopology_iff` (universal property): for any topological
  space `(X, t)` and any function `f : ℚ ⊗[ℤ] M → X`,
  `Continuous[finalTopology M, t] f ↔ ∀ q : ℚ, Continuous[_, t] fun x : M => f (q ⊗ₜ[ℤ] x)`.
  Both sides unfold, by `continuous_def` and the open-set characterization, to
  the statement that `(fun x => q ⊗ₜ[ℤ] x) ⁻¹' (f ⁻¹' V)` is open for every
  `t`-open `V` and every `q`. The proof only reorders the two universal
  quantifiers. The topology `t` is an implicit argument rather than an instance
  argument, so the criterion also applies when `X` is itself `ℚ ⊗[ℤ] N` with
  `finalTopology N` and no instance in scope.
- `continuous_of_forall_continuous_tmul`: the direction `←` of the criterion,
  stated separately for use with `refine`.
- `Rationalization.continuous_tmul` (protected): for every `q : ℚ`, the chart
  `fun x : M => q ⊗ₜ[ℤ] x` is continuous from `M` to `finalTopology M`. The
  preimage of a `finalTopology`-open set under the `q`-th chart is open by
  definition.
- `Rationalization.continuous_smul` (protected): for every `q : ℚ`, including
  `q = 0`, the map `fun y : ℚ ⊗[ℤ] M => q • y` is continuous from
  `finalTopology M` to itself. The scalar action is Mathlib's left action of `ℚ`
  on the left tensor factor (`TensorProduct.leftHasSMul`, underlying
  `TensorProduct.leftModule`). By the criterion it suffices to treat each chart
  `r`. By `TensorProduct.smul_tmul'`, `q • (r ⊗ₜ x) = (q * r) ⊗ₜ x`, so the
  composite is the `(q * r)`-th chart. No case distinction on `q` is needed; for
  `q = 0` this composite is the zero chart.
- `continuous_baseChange`: for a continuous additive homomorphism
  `f : M →+ N`, the existing algebraic scalar extension
  `f.toIntLinearMap.baseChange ℚ : ℚ ⊗[ℤ] M →ₗ[ℚ] ℚ ⊗[ℤ] N` is continuous from
  `finalTopology M` to `finalTopology N`. This is the same expression as the one
  used by `Langlands.AbelianScheme.Tate.rationalMonodromyMap`. By the criterion
  and `LinearMap.baseChange_tmul`, the composite with the `q`-th chart of `M` is
  `x ↦ q ⊗ₜ f x`, the `q`-th chart of `N` after `f`. The preimage of a
  `finalTopology N`-open set under it is `f ⁻¹'` of an open subset of `N`, hence
  open. Only the continuity of `f` is used; neither group needs a topological
  group structure.

`continuous_tmul` and `continuous_smul` are protected because Mathlib already
has `TensorProduct.continuous_tmul` and the root name `continuous_smul`
(exported from the class `ContinuousSMul`). Without protection,
`open Langlands.Topology.Rationalization` would make these names ambiguous. Refer to them as `Rationalization.continuous_tmul` and
`Rationalization.continuous_smul` (or by their full names).

Every declaration depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Scope

This module provides only the intrinsic layer. It proves none of the following:
continuity of addition or negation, the Hausdorff property, local compactness,
an embedding or open-embedding property of the chart `x ↦ 1 ⊗ₜ x`, that
multiplication by a nonzero rational is a homeomorphism, or joint continuity of
any group action or of the scalar action with any topology on `ℚ`. The
hypothesis of the parent task 9be1dc18 that multiplication by each positive
natural number is an open embedding `M → M` is not used here. These results,
and the action assembly, belong to that parent task, and the actual geometric
monodromy action belongs to task 74795b53. Without further hypotheses on `M`
the topology can be degenerate. For example, the charts need not be injective,
and the topology need not be Hausdorff. No such property is claimed.

## Provenance

This is internal project mathematics. The construction is the general notion of
the final topology of a family of maps, which Mathlib expresses as a supremum of
coinduced topologies. Here it is applied to the family of tensor charts
`x ↦ q ⊗ₜ x`. The lemmas are elementary consequences of the definition. They
are not quoted from a literature source, and no literature theorem is claimed.
The construction was requested by task 5bf0c35e, which is a prerequisite of the
generic rationalization topology task 9be1dc18. The algebraic ingredients come
from Mathlib's `TensorProduct`: the carrier `ℚ ⊗[ℤ] M`, the left `ℚ`-action,
`LinearMap.baseChange` and `AddMonoidHom.toIntLinearMap`.
