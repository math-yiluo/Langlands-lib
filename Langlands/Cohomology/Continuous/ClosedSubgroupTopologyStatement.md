# Finite-tuple extension and neighborhood detection for closed subgroups

Author: Worker 205. This pair states two topological propositions about finite
tuples in profinite groups and their conjunction. It proves nothing; each
proposition is a `Prop`-valued definition whose proof is a separate
contribution.

All three declarations are in the namespace `Langlands.Continuous` and have
one universe parameter `u`. The group `G` and the target `Y` both live in
`Type u`. In each clause, `G` carries `[Group G] [TopologicalSpace G]
[IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]`,
so `G` is a compact Hausdorff totally disconnected (profinite) topological
group. `Y` carries `[TopologicalSpace Y] [DiscreteTopology Y]` and no algebraic
structure.

Subgroups are Mathlib's `ClosedSubgroup G`. The coercion of `H : ClosedSubgroup G`
to a type is the subtype of elements of `H`, with the actual subspace topology
induced from `G`. Tuples `Fin n → H` and `Fin n → G` carry the product
topology. For `x : Fin n → H`, the tuple `fun i => (x i : G)` is `x` composed
coordinatewise with the subtype inclusion. `C(X, Y)` is Mathlib's bundled type
of continuous maps.

## `ClosedSubgroupTupleExtension`

For every such `G` and `Y`, every closed subgroup `H : ClosedSubgroup G`, every
natural number `n`, and every continuous map `f : C((Fin n → H), Y)`, there
exists a continuous map `F : C((Fin n → G), Y)` such that
`F (fun i => (x i : G)) = f x` for every `x : Fin n → H`.

So every continuous discrete-valued function on `n`-tuples of `H` is the
restriction of a continuous function on `n`-tuples of `G`. The subgroup `H` is
not assumed open or normal. `Y` is not assumed nonempty: `Fin n → H` always
contains the identity tuple, so `f` already supplies a value in `Y`. The
case `n = 0` is included.

## `ClosedNormalTupleAgreement`

For every such `G` and `Y`, every closed subgroup `H : ClosedSubgroup G`, given
the hypothesis `H.toSubgroup.Normal`, every natural number `n`, and every pair of
continuous maps `f g : C((Fin n → G), Y)`, suppose that
`f (fun i => (x i : G)) = g (fun i => (x i : G))` for every `x : Fin n → H`.
Then there exists `U : OpenNormalSubgroup G` with
`H.toSubgroup ≤ U.toSubgroup` such that `f x = g x` for every
`x : Fin n → G` satisfying `x i ∈ U` for all `i`.

Thus agreement on all `H`-tuples is detected on an open normal subgroup
containing `H`. Normality is an explicit hypothesis, not an instance argument.
`H` is not assumed open. The case `n = 0` is included. Stating the conclusion
with `x : Fin n → U` and coordinatewise subtype inclusion would be equivalent;
this pair uses ambient tuples with coordinatewise membership.

## `ClosedSubgroupTupleApproximation`

`ClosedSubgroupTupleApproximation.{u}` is
`ClosedSubgroupTupleExtension.{u} ∧ ClosedNormalTupleAgreement.{u}`.
Either clause can be used on its own by its name or by projection.

## Provenance

These propositions are internally derived topology prerequisites, not
quotations from the literature. They support the closed-normal continuous
cohomology descent statement (task `72beaba6-b4c7-46d3-a92e-1c0436d470f3`)
within the unramified `H^2` exhaustion work (task
`3263cf33-f7d5-406a-95a6-75a5b789e94d`). They are not arithmetic assertions
from Serre's *Local Fields*. No literature source is cited.

The intended proof route uses two named facts. One is the published
Library theorem
`Langlands.Continuous.exists_finite_quotient_factor`, in
`Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof`. For a compact
topological group, it factors a continuous discrete-valued map on `n`-tuples
through an open normal quotient. The other is Mathlib's
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`. It finds an
open normal subgroup inside each open neighbourhood of `1` in a compact
totally disconnected group.

- For the extension clause, `H` is compact because it is closed. One first
  factors `f` through a finite quotient of `H` by an open normal subgroup `K`
  of `H`. Next one chooses an open normal subgroup `N` of `G` whose
  intersection with `H` lies in `K`. Then `f` depends only on the image of a
  tuple in `Fin n → G ⧸ N`. Since this quotient tuple space is discrete, the
  induced function on the image of the `H`-tuples extends arbitrarily to all
  of it. Composing with the quotient map gives `F`.
- For the agreement clause, one factors the pair `(f, g)` through one ambient
  quotient by `N`, then takes `U = H ⊔ N`. This is open because it contains
  `N`, and normal because `H` and `N` are normal. Each tuple in `U` has the same
  quotient image as a tuple in `H`.

This route is a guide for the separate proof task. This pair implements no
proof.

The `[T2Space G]` hypothesis is included because the task specifies compact
Hausdorff groups. The proof route above does not need it.

## Environment

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0
(`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The module imports only
`Mathlib.Topology.Algebra.Group.ClosedSubgroup`,
`Mathlib.Topology.Algebra.OpenSubgroup` and
`Mathlib.Topology.ContinuousMap.Defs`.
