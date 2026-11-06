# The full intersection of a maximal torus with the actual derived subgroup

Worker 1376, adapting Worker 1435's published intersection reduction.

`Langlands.GroupScheme.derivedMaximalTorusIntersection` proves exactly
`Langlands.GroupScheme.DerivedMaximalTorusIntersectionStatement.{u}`.
For every field `k : Type u`, connected reductive group scheme `G`, supplied
actual derived inclusion `d : D → G`, and maximal torus `t : T → G`, the
entire scheme-theoretic pullback `T ×_G D` is a torus. The universe and
characteristic are unrestricted. There are no additional hypotheses on the
field, the torus, or the derived source.

The proof specializes the full-pullback argument in
[`MaximalTorusIntersectionReduction`](MaximalTorusIntersectionReduction.md)
using published geometric constructions. It does not assume either of
that reduction's two structural premises.

Extend scalars to `K = AlgebraicClosure k`. The published field-extension
theorem gives connected reductivity of `G_K`, and the published derived
base-change theorem makes the given `d_K` an actual derived inclusion.
`maximalTorusBaseChange` makes the given `t_K` maximal. Its smoothness and
affineness hypotheses follow from connected reductivity of `G`.

Over `K`, the published
`IsDerivedSubgroup.exists_compatible_maximalTorus_of_isAlgClosed` constructs
a maximal torus `j : A → D_K` with a closed map `e : A → T_K` and the exact
commuting square `e ≫ t_K = j ≫ d_K`. This retains the original
scalar-extended ambient torus and derived inclusion. The unconditional
`IsDerivedSubgroup.isConnectedReductive` from the imported reduction proves
connected reductivity of the actual source `D_K`.

The published two-input centralizer assembly
`algClosedMaximalTorusCentralizer_fromQuotient` applies to `j`. Its inputs
are discharged by the published exact proofs `dynamicCentralizerReductive`
and `solvableTorusQuotient`. It therefore proves the all-test-scheme equality
`torusCentralizer j = SubgroupFunctor.range j`. No centralizer proposition
remains a hypothesis.

Apply
`isTorus_subgroupIntersection_of_selfCentralizing_of_reflection` with the
identity of `D_K` as its first map. The closed derived inclusion is monic;
commutation in the commutative target `T_K` therefore reflects to `D_K`.
The helper identifies the full pullback `D_K ×_{G_K} T_K` with the
self-centralizing torus `A`, using equality of represented subgroup
functors on all test schemes. Pullback symmetry gives the torus property
of `T_K ×_{G_K} D_K`. This step retains all scheme structure, including
nonreduced structure.

Finally, `subgroupIntersectionBaseChangeIso` compares this pullback with
the base change of the original `T ×_G D`, and
`IsTorus.of_baseChange` descends the torus property along the field
extension. The statement pair and all its imported definitions are
unchanged.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
source `kaletha-prasad-2023-bruhat-tits-new-approach`, §2.6(a), printed
p. 93 / PDF p. 124. It states the stronger maximality of the intersection.
The target and this proof retain its torus consequence. The authors'
*Corrections and additions*, source `kaletha-prasad-2024-corrections`,
version 1 November 2024, PDF p. 25, does not change §2.6(a).
The implemented route is the published geometric compatible-torus
construction, selfcentralization, the full-pullback comparison, and descent;
the imported results retain their own provenance and authorship.
