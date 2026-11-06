# Actual parahoric-building data of every local-field torus

This internally derived construction works at every universe `u`, for every
nonarchimedean local field `F` and every actual commutative group scheme `T`
satisfying `IsTorus T.toGrp`. It constructs `ParahoricBuildingData T.toGrp`.
There is no supplied building datum, root valuation, centralizer datum, derived
cover or unramified splitting-field premise.

The underlying valuation-building datum is exactly
`ValuationBuildingData.ofTorus T hT`. That constructor chooses an actual maximal
split subtorus, represents its centralizer by `T` itself, proves the real
character comparison from the published torus theorems, and constructs the
`localFieldOrder F`-normalized empty-root apartment.

For the zero-subgroup datum, `commutativeDerivedCoverData` constructs the actual
simply connected derived cover of `T.toGrp`. Both source groups are the actual
trivial group scheme, the covering morphism is its identity, and the derived
inclusion is the unit subgroup. The same construction applies to the actual
base change of the centralizer over `UnramifiedClosure F`: the centralizer is
definitionally `T.toGrp`, base change preserves the actual torus property, and
commutative base change preserves commutativity. These are full universal covers,
not additional supplied existence hypotheses.

`ParahoricBuildingData.ofDerivedCovers` then supplies the remaining actual
zero-subgroup choices: a maximally split maximal torus of that unramified
centralizer and a finite Galois splitting field inside `SeparableClosure F`.
The resulting zero-subgroup datum uses precisely the maximal split torus and
centralizer of the chosen valuation datum. The projection theorem is
reflexivity, so the original reduced quotient and rational-point action are
preserved. The full existing `SatisfiesApartmentAxioms` conclusion also follows
from the underlying torus constructor.

The provenance is an internal assembly of the three named constructors and the
proved arbitrary-field-extension theorem `IsTorus.baseChange`. This unit proves
torus data existence and the single-apartment predicate. It does not assert the
other building-level axiom families or existence for general connected
reductive groups. The unrestricted `RootValuationBuildingConstructionStatement`
remains a parent-task obligation.
