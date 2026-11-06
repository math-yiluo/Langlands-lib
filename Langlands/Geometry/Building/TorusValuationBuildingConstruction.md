# Actual valuation-building data of a field torus

This is an internal construction from proved torus structure and the existing
root-free valuation-building constructor. For every actual commutative field
group scheme that is a torus, it constructs its actual centralizer data at any
maximal split subtorus. Over every nonarchimedean local field it chooses the
maximal split subtorus and constructs `ValuationBuildingData` for the original
torus, with no supplied apartment, root valuation or centralizer datum.

A torus is connected reductive by the published field-splitting and
field-extension reflection theorem. Its largest split subtorus exists and is
maximal split. Since the ambient group is commutative, its embedding is
central and the whole torus, through the identity inclusion, represents the
actual all-test centralizer.

The character comparison uses two published results with no structural
premise: restriction of rational characters to a maximal split subtorus of a
torus is injective, and restriction to a split component of a connected
reductive group has finite-index image. The maximal split subtorus is the
split component because the group is commutative. The existing real
character comparison therefore proves precisely the bijectivity field of
`CentralizerDatum`. The centralizer group is the original torus, its ambient
inclusion is the identity, and the factor map is the original split-subtorus
embedding.

Centrality also makes the actual relative roots empty: restricting any
alleged root along the identity of the split torus gives zero by the
published central-root restriction theorem, contradicting that a root is
nonzero. The existing normalized empty-family constructor then supplies all
root-valuation and apartment data at `localFieldOrder F`. Its original
reduced quotient and rational-point action are unchanged.

`ValuationBuildingData.ofTorus` chooses these actual data at every universe
`u`, and `ofTorus_satisfiesApartmentAxioms` proves the full existing
single-apartment predicate, including V 6, V 7 and AS 2–AS 5. This does not
construct `ParahoricBuildingData`, its actual derived covers or zero data,
a polysimplicial realization, an apartment splitting or the unrestricted
five-axiom theorem. Those remain obligations of the parent task. The
constructor covers split and nonsplit tori without a characteristic
restriction.
