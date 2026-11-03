# Actual roots and ambient action-weight sign support

Author: Worker 1323.

This is derived support infrastructure for
`Langlands.GroupScheme.RelativeRootSignInclusionsStatement`. It identifies the
published actual relative roots with the nonzero part of the ambient
conjugation-action weight support, and converts root-sign containment into
containment of sign semigroups restricted to that support.

The defined set `RelativeRoot.adjointWeightSupport i` is
`{χ | weightSpace i χ ≠ ⊥}`: the full support of the adjoint weight spaces.
It includes the zero character exactly when its weight space is nonzero.
Unlike `relativeRoots i`, the definition imposes no nonzero-character condition.
This is an internal set construction from the published weight spaces.

The scope is any field `k : Type u`, any commutative group scheme `S` over
`Spec k`, any affine group scheme `G` over `Spec k`, and any homomorphism
`i : S.toGrp → G`. The statements retain the original universe and every
coefficient extension in the definitions of the weight spaces. Splitness,
smoothness, connectedness, maximality, and reductivity are not needed for this
conversion.

## Provenance and implemented proof

The module imports the published `ActionWeightComparisonProof`, whose theorem
`actionWeightSpace_conjugation` identifies the intrinsic action weight space
with the original adjoint weight space `weightSpace i χ`. The published
definition `relativeRoots i` consists of characters `χ ≠ 0` with
`weightSpace i χ ≠ ⊥`. These two facts, rather than an additional structural
theorem about reductive groups, supply the entire mathematical input.

`mem_actionWeightSupport_conjugation_top` first observes that the point
membership condition in `actionWeightSupport b ⊤` always holds. A nonzero
vector in the action weight space is therefore exactly a witness that the
space is nonzero, using `Submodule.ne_bot_iff`. The conjugation comparison
then gives the claimed adjoint weight-space test.

`adjointWeightSupport_eq_actionWeightSupport_conjugation_top` identifies the
defined adjoint support with the ambient conjugation-action support by
extensionality and that membership test.
`mem_relativeRoots_iff_adjointWeightSupport` applies the definition of actual
roots. Rewriting the adjoint support with the preceding equality gives
`mem_relativeRoots_iff_actionWeightSupport_conjugation_top`. Its set form,
`relativeRoots_eq_actionWeightSupport_conjugation_top_diff_zero`, removes
the singleton zero from the ambient support. No assertion that the zero
weight space is nonzero is made.

`rootSupport_imp_iff_actionWeightSupport_imp` extends an implication
`P χ → Q χ` from the actual roots to the ambient support when its
zero-character instance is known. For a nonzero supported character the
previous membership equivalence supplies an actual root. At zero the
explicit zero case applies. Restriction proves the converse.

`nonnegative_rootSupport_iff` specializes this observation to the two
nonnegative pairing conditions. The zero character pairs to zero, so the
target condition at zero holds. `positive_rootSupport_iff` uses the
strictly positive pairing conditions; their antecedent at zero is false.
The two `_inter_subset` variants rewrite these quantified implications as
an intersection of the ambient support with the source sign semigroup
being a subset of the target sign semigroup.

These lemmas do not identify dynamic subgroups with semigroup subgroups
or prove their geometric realization. They supply the root-support
conversion needed when applying those independently proved structural
comparisons to the exact inclusion target. They also apply when the
actual root set is empty.
