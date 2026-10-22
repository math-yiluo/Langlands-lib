# Closed subgroup tuple approximation: proof

The module `Langlands.Cohomology.Continuous.ClosedSubgroupTopologyProof` proves the published proposition `Langlands.Continuous.ClosedSubgroupTupleApproximation.{u}` from `Langlands.Cohomology.Continuous.ClosedSubgroupTopologyStatement`. That proposition is the conjunction of `ClosedSubgroupTupleExtension.{u}` and `ClosedNormalTupleAgreement.{u}`. The module also imports `Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof` for the Library theorem `Langlands.Continuous.exists_finite_quotient_factor`. It does not change the statement module.

The final theorem `Langlands.Continuous.closedSubgroupTupleApproximation` has exactly the type `ClosedSubgroupTupleApproximation.{u}`. Each clause can also be used on its own, either as a component of that theorem or directly through the helper theorems `exists_closedSubgroup_tuple_extension` and `exists_openNormal_tuple_agreement`. The helper names are fixed because the downstream closed-normal cohomology descent proof imports them.

## Setting

All declarations are in the namespace `Langlands.Continuous` and use one universe `u`. The section variables are `G Y : Type u`. Here `G` is a topological group that is compact and totally disconnected, and `Y` is a discrete topological space. Subgroups carry the subspace topology, and tuple spaces `Fin n → H` and `Fin n → G` carry the product topology.

The helpers do not assume `[T2Space G]`. The final theorem receives that instance from the target proposition and does not use it. `exists_openNormal_tuple_agreement` also omits `[TotallyDisconnectedSpace G]` (via `omit`), because it only uses compactness. No result assumes that `Y` is inhabited, that `H` is open, or that `n` is positive. Tuple length `0` is handled by the same argument as every other length.

## `exists_ambient_normal_refinement`

Statement: for every `H : Subgroup G` and every `K : OpenSubgroup H`, there is `N : OpenNormalSubgroup G` with `N.toSubgroup.comap H.subtype ≤ K.toSubgroup`. In words, the trace on `H` of some ambient open normal subgroup lies in `K`.

Proof. `K` is open in the subspace topology, so `isOpen_induced_iff` gives an open set `V ⊆ G` whose preimage under `Subtype.val` is `K`. The identity of `H` lies in `K`, so `1 ∈ V`. Mathlib's `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` applies to compact totally disconnected topological groups, and it gives an open normal subgroup `N` of `G` with `N ⊆ V`. If `x : H` and `(x : G) ∈ N`, then `x` lies in the preimage of `V`, which is `K`. This helper does not use closedness of `H`.

## `exists_closedSubgroup_tuple_extension`

Statement: for every `H : ClosedSubgroup G`, every `n : ℕ` and every `f : C((Fin n → H), Y)`, there is `F : C((Fin n → G), Y)` with `F (fun i => (x i : G)) = f x` for all `x : Fin n → H`.

Proof. `H` is a topological group: the instance is transferred from `H.toSubgroup`. `H` is also compact, by Mathlib's instance for closed subgroups of compact groups. So `exists_finite_quotient_factor` applies to `H`. It gives an open normal subgroup `K` of `H` and a continuous map on `Fin n → H ⧸ K` that agrees with `f` after the coordinatewise quotient map.

`exists_ambient_normal_refinement` then gives an open normal subgroup `N` of `G` whose trace on `H` lies in `K`. Let `π : (Fin n → H) → (Fin n → G ⧸ N)` take the ambient quotient class of each coordinate. Suppose `π x = π y`. Then `(x i)⁻¹ * y i ∈ N` for every `i`, so this element lies in `K`, and `x i` and `y i` have the same image in `H ⧸ K`. The factorization then gives `f x = f y`, so `f` factors through `π`.

`N` is open, so `G ⧸ N` is discrete by `QuotientGroup.discreteTopology_iff`. The finite product `Fin n → G ⧸ N` is therefore discrete, and every function on it is continuous. Let `Q` be the function `Function.extend π f d`, where the default `d` is constantly the value of `f` at the identity tuple. That tuple always exists, so no inhabitedness of `Y` is needed.

Define `F x` as `Q` applied to the tuple of ambient quotient classes of `x`. `F` is continuous because it composes `Q` with coordinatewise continuous quotient projections. For `x : Fin n → H`, `Function.FactorsThrough.extend_apply` gives `F (fun i => (x i : G)) = Q (π x) = f x`.

## `exists_openNormal_tuple_agreement`

Statement: let `H : ClosedSubgroup G` with an instance `[H.toSubgroup.Normal]`, let `n : ℕ`, and let `f g : C((Fin n → G), Y)` satisfy `f (fun i => (x i : G)) = g (fun i => (x i : G))` for all `x : Fin n → H`. Then there is `U : OpenNormalSubgroup G` such that `H.toSubgroup ≤ U.toSubgroup`, and `f x = g x` for every `x : Fin n → G` with `x i ∈ U` for all `i`.

Proof. The pair map `x ↦ (f x, g x)` into the discrete space `Y × Y` is continuous. `exists_finite_quotient_factor` applied to it gives an open normal subgroup `N` of `G` and a continuous `F` with `F (fun i => (x i : G ⧸ N)) = (f x, g x)` for all `x`.

Let `U` be the join `H.toSubgroup ⊔ N.toSubgroup`, packaged as an open normal subgroup. It is open because it contains the open subgroup `N` (`Subgroup.isOpen_mono`), and it is normal because it is a join of normal subgroups. `le_sup_left` gives `H.toSubgroup ≤ U.toSubgroup`.

Let `x` have all coordinates in `U`. By `Subgroup.mem_sup_of_normal_right`, each coordinate is a product `x i = h i * t i` with `h i ∈ H` and `t i ∈ N`; the factors are chosen with `choose`. Let `y : Fin n → H` be the tuple of the `h i`. Since `t i ∈ N`, the tuples `x` and `y` have the same coordinatewise class modulo `N`. Hence `(f x, g x)` equals `(f y, g y)`, both being `F` of that class tuple. The hypothesis gives `f y = g y`, so `f x = g x`. When `n = 0` the same argument applies, with the empty tuples.

## `closedSubgroupTupleApproximation`

The theorem splits the conjunction with `constructor`. For each clause it introduces the quantified group, target, instances (including the unused `T2Space G`) and data. The first clause then applies `exists_closedSubgroup_tuple_extension`. For the second clause, the explicit normality hypothesis `H.toSubgroup.Normal` is installed as a local instance, and the theorem applies `exists_openNormal_tuple_agreement`.

Development inspection reports universe parameter `u` and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

These are internal derivations: generic topology prerequisites for closed-normal continuous cohomology descent, which is part of the unramified H² exhaustion work. No literature is cited and the module states no literal literature claim. The arguments use only the published Library theorem `exists_finite_quotient_factor` and Mathlib topology and subgroup lemmas. The module asserts no local-field arithmetic result and no cohomology theorem.

Worker 102 wrote the Lean proof in a shared draft, and it is submitted unchanged. This Markdown replaces the draft's development-status wording with a description of the submitted proof.
