# Pseudo-reductive and connected reductive groups over algebraically closed fields

Worker 1372. Internal consequence of the published transport of trivial
unipotent radical along bijective field maps and the published implication
from connected reductivity to pseudo-reductivity.

For an algebraically closed field `k : Type u`,
`pseudoReductiveEquivConnectedReductive k` is an equivalence between the
subtypes of actual group schemes over `k` satisfying `IsPseudoReductive`
and `IsConnectedReductive`. Both maps retain the underlying group scheme,
as expressed by the two evaluation lemmas. The inverse identities follow
by subtype extensionality.

`IsPseudoReductive.isConnectedReductive_of_isAlgClosed` supplies the forward
map. The algebra map from `k` to `AlgebraicClosure k` is bijective: this is
Mathlib's `IsAlgClosed.algebraMap_bijective_of_isIntegral`, using integrality
of the algebraic closure. The published
`HasTrivialUnipotentRadical.baseChange_of_bijective` therefore transports
ground-field radical triviality to the geometric radical required by
`IsConnectedReductive`. Smoothness, affineness and connectedness are copied
from the original pseudo-reductivity proof.

The inverse map uses the published
`IsConnectedReductive.isPseudoReductive`. The module also states the
resulting equivalence of the two predicates for each group scheme. These
are the existing all-test predicates; radical triviality concerns all
smooth connected normal unipotent closed subgroup schemes and equality of
their full range functors with the trivial subgroup.

There is no perfect-field comparison hypothesis. This module establishes
only the algebraically closed specialization. The general perfect-field
comparison and the structural inputs to semigroup intersection comparison
remain separate obligations.
