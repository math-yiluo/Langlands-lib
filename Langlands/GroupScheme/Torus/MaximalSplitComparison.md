# Comparing maximal tori with maximal split tori

Author: Worker 1354.

This is internal infrastructure derived directly from the existing
`IsTorus`, `IsSplitTorus`, `IsMaximalTorus` and `IsMaximalSplitTorus`
definitions. It applies to every field `k : Type u` and every actual
embedding from a commutative group scheme into a group scheme over `Spec k`.
No hypothesis on the ambient group's smoothness, affineness, connectedness or
reductivity is required.

`ToriAreSplit k` is the explicit property that every group scheme satisfying
`IsTorus` over `k` satisfies `IsSplitTorus` over `k`. Defining this proposition
does not prove it for any field. The lemma `ToriAreSplit.isTorus_iff`
combines this property with the published `IsSplitTorus.isTorus`.

`IsMaximalTorus.isMaximalSplitTorus` assumes that the given maximal torus is
split. A competing closed split torus is a torus, so the original maximality
condition makes every factor map through that competitor an isomorphism.
The original closed immersion and the supplied splitting witness give the
split-subtorus condition.

Conversely, `IsMaximalSplitTorus.isMaximalTorus` assumes `ToriAreSplit k`.
The source of the given maximal split torus is a torus. Each competing closed
torus is split by the explicit hypothesis, so maximality among split tori
forces the required factor map to be an isomorphism. The final
`ToriAreSplit.isMaximalTorus_iff` packages these two directions.

The maps and their closed-immersion conditions remain the same throughout;
these lemmas compare the existing predicates on the same actual map.
They do not construct a maximal torus or a conjugating point, do not establish
that all tori over an algebraically closed field are split, and do not prove
any field-extension preservation theorem. Those structural results remain
separate obligations. No new external mathematical source is used.

The existing `IsMaximalTorus.isMaximalSplitTorus` declaration is shared from
`Torus.MaximalSplitComparison`, with its original type and proof.
`Reductive.RootDatumAssembly` imports this common torus comparison.
