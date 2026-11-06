# The full maximal-torus preimage in a simply connected derived cover

Worker 1669, adapting Worker 1614's published preimage reduction.

`Langlands.GroupScheme.derivedCoverMaximalTorusPreimage` proves exactly
`Langlands.GroupScheme.DerivedCoverMaximalTorusPreimageStatement.{u}`.
For every field `k : Type u`, supplied maps `d : D → H`, `π : C → D`,
and maximal-torus embedding `i : T → H`, the hypotheses
`IsSimplyConnectedDerivedCover d π` and `IsMaximalTorus i` imply that the
entire scheme-theoretic pullback `C ×_H T` is a torus. The universe,
characteristic and field are unrestricted. The statement pair and its
imports are unchanged.

Extend scalars to `K = AlgebraicClosure k`. Connected reductivity of `H`,
`D` and `C` follows from the supplied cover and the published
field-extension theorem. The derived inclusion remains an actual derived
inclusion by `derivedSubgroup_baseChange_eq_of_field`, and the central
isogeny remains a central isogeny. The unconditional
`maximalTorusCentralizer` theorem makes the original maximal torus
self-centralizing on every test scheme. The published self-centralizer
base-change criterion then makes its extension `T_K → H_K` maximal.
This step does not require base change of algebraic simple connectedness.

Over `K`, the published
`IsDerivedSubgroup.exists_compatible_maximalTorus_of_isAlgClosed`
(module `Rational.GeometricSubgroupTorus`, Worker 1632) gives a split
maximal torus `s : S → D_K` and a closed torus map `e : S → T_K` with
`e ≫ i_K = s ≫ d_K`. Its proof uses the published geometric
maximal-torus conjugacy theorem, finite-Galois splitting, and the
normal-subgroup torus construction. All geometric hypotheses follow from
connected reductivity of `H_K`. The stronger arbitrary-field proposition
`DerivedMaximalSplitTorusStatement` is not a premise of this proof.

The proved `centralIsogenySplitMaximalTorusLift` lifts `S` through `π_K`
to a maximal torus `j : A → C_K` and a torus map `f : A → S` with
`j ≫ π_K = f ≫ s`. Composing the two commuting squares gives
`j ≫ π_K ≫ d_K = f ≫ e ≫ i_K`. The unconditional
`maximalTorusCentralizer` theorem gives
`torusCentralizer j = SubgroupFunctor.range j`.

Apply the published
`isTorus_subgroupIntersection_of_selfCentralizing_of_reflection`
(module `Torus.SelfCentralizingPullback`, Worker 1669).
The full pullback over `K` centralizes `A`: after mapping into the
commutative ambient torus, its elements commute with the image of `A`;
the monic derived inclusion reflects this commutation to `D_K`.
`IsCentralIsogeny.torusCentralizer_comap` (Worker 1614) reflects
centralization through `π_K` on every test scheme. The comparison therefore
identifies the actual pullback with the self-centralizing source torus
`A`, so that entire pullback is a torus.

Finally, `subgroupIntersectionBaseChangeIso` identifies this pullback with
the scalar extension of the original `C ×_H T`, and
`IsTorus.of_baseChange` descends the torus property to `k`. The proof keeps
all scheme structure and adds no smoothness or étaleness assumption on the
central cover. In particular, its finite central kernel may be nonreduced.

The provenance is an internal composition of the named published
constructions and proofs. It follows the full-pullback comparison and
descent route of `DerivedCoverMaximalTorusPreimageReduction`, with its
self-centralizer input supplied by the unconditional Library proof and
its derived-torus input replaced by the proved geometric compatible-torus
construction. No structural proposition remains an extra hypothesis.
