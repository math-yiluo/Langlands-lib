# The first cyclic-tail functor is the intrinsic relative root functor

`RelativeRoot.cyclicRootFunctorComparison` proves the exact existing proposition
`RelativeRoot.CyclicRootFunctorComparisonStatement.{u}`. For every field in any
universe, a smooth affine group scheme, a split torus, an arbitrary homomorphism
from that torus to the group, and every nonzero character, the first
`weightFiltration` for conjugation equals the intrinsic character-orbit subgroup
functor. This is equality on every test scheme. The character need not occur
as a relative root or be primitive, and the ambient group need not be connected.

The proof uses the actual subgroup functors, differential weight spaces,
scheme-theoretic character kernel and descended actions. It first supplies the
remaining connectedness input. For any multiplicative-group action on an affine
group over a field, the existing semidirect-product construction uses the same
group scheme as the representative of the ambient cocharacter's dynamic
unipotent functor and of the original action's identity-limit functor.
`AutomorphicAction.Affine.connectedSpace_unipotentScheme` therefore applies
`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent` to the semidirect
product. This needs no smoothness or connectedness premise.
`connectedSpace_of_isRepresentedBy_unipotent` transfers the result to every
representative along the canonical isomorphism of all-test representatives.

`subgroup_isSmoothConnectedClosed_of_ne_zero` applies the existing
`kernelCentralizerStructure` to the actual character kernel. Its smooth closed
centralizer representative is affine because it is closed in the affine ambient
group. The nonzero character is an fpqc map to the multiplicative group by
`characterFpqc`, so the conjugation action on that centralizer descends to the
actual `quotientAction`. Its identity-limit representative is smooth by the
arbitrary-action smoothness theorem, connected by the preceding semidirect
argument, and closed in the centralizer. Composing with the centralizer inclusion
gives a smooth connected closed representative of the intrinsic root functor:
`quotientActionComparison` identifies the functors, and composition of represented
subgroups identifies their all-test images.

For the reverse containment, `tangentSubmodule_subgroup` gives exactly the first
positive cyclic weight span as the root functor's intrinsic tangent submodule.
The split-torus support theorem turns that equality into containment of its
actual tangent support in `cyclicTail a 1`. Together with the smooth connected
closed representative and `subgroup_isStable`, this makes the root functor itself
an admissible generator of the defining semigroup subgroup. The defining
generator inclusion gives containment in the first `weightFiltration`.

`weightFiltration_one_le_subgroup`, proved in
[`CyclicWeightContraction`](CyclicWeightContraction.md), supplies the other
containment: every admissible generator contracts through the specified
character, and composition transports its actual identity-limit extensions into
the intrinsic root functor. Antisymmetry gives
`weightFiltration_one_eq_subgroup`. Introducing exactly the hypotheses of the
published target then proves `cyclicRootFunctorComparison`.

This proof is an internal assembly of the imported constructions and proved
results. It assumes neither general semigroup realization nor the full
`DynamicConnectedStatement`. The target and its imported Lean and Markdown
declarations are unchanged.
