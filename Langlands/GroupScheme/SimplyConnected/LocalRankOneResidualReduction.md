# Conditional reduction to three residual actual index patterns

Author: Worker 177.

This internal proof assembly concerns the exact five alternatives in
`LocalRankOneTitsIndexStatement`. Its conclusion remains conditional. In
particular, the file does not prove the unconditional enumeration, the
arithmetic exclusion of higher type B or G2, or the inner and trialitarian
type-D4 exclusions.

`localRankOneTitsIndex_or_residual_of_components` assumes:

1. `LocalAnisotropicCartanComponentsStatement`;
2. `NormOneCenterAutomorphismOppositeStatement`;
3. `RankOneTypeEKernelCenterMovementStatement`;
4. an actual index `d` with `HasIrreducibleCartanType`, and the usual local-field,
   simply connected, absolutely almost-simple and split-rank-one hypotheses.

It proves the disjunction of the five exact desired alternatives and
`d.HasResidualRankOneIndex`. The latter is a concrete property of the actual
matrix, marking and full star action defined in `LocalRankOneResidualIndices`,
not a premise or a conclusion about the existence of a proof.

The proof exhausts the nine families in `HasIrreducibleCartanType`:

| Family | Implemented reduction |
| --- | --- |
| A | Split on triviality of the full star action. Apply the exact inner-A or outer-A index theorem. |
| B | In rank two, use the B2-to-C2 numbering and exact index theorem. Otherwise, the component reduction marks one of the final two vertices and gives the higher-B residual pattern. |
| C | Apply the complete local type-C index theorem, including its rank bound. |
| D | In ranks at least five, the component reduction gives exactly inner D5. In rank four, first obtain the central marking. A nontrivial full star action with a globally fixed leaf gives the exact outer-D4 index after renumbering. The trivial-star and no-fixed-leaf cases give the D4 residual pattern. |
| E6, E7 | The component reductions give trivial full star and the branch marking. The two explicit centre prerequisites contradict the degree-six or degree-seven actual norm-one kernel model. |
| E8, F4 | Apply the existing conditional component exclusions. |
| G2 | The exact long-root marking and trivial full star give the G2 residual pattern. |

The D4 absence condition concerns a leaf fixed simultaneously by every
Galois element. No claim that all diagram automorphisms have a common fixed leaf
is used. Every resulting index retains an equivalence of the entire vertex type,
every ordered Cartan entry, the distinguished subset exactly, and the full
absolute Galois action required by the corresponding predicate.

`localRankOneTitsIndex_or_residual_of_componentFactor` replaces the first
premise with `SemisimpleTitsComponentFactorStatement`. It uses the published
unconditional `localAnisotropicTypeA` theorem for the other premise of
`localAnisotropicCartanComponents_of_componentFactor`; no local type-A
classification assertion is left implicit.

Finally, `localRankOneTitsIndex_of_remaining_inputs` returns the exact
`LocalRankOneTitsIndexStatement.{u}` under five explicit inputs: absolute Cartan
classification, actual component realization, the norm-one/opposite-algebra
statement, E-type kernel centre movement, and exclusion of the concrete residual
patterns for every local simply connected absolutely almost-simple rank-one
index. It applies the preceding disjunction and contradicts its residual branch.
This is a conditional theorem and does not discharge any of these inputs.

The provenance is internal composition of the imported actual-index reductions;
no independent transcription of a source theorem is asserted. The final
group-model classification and local Kneser--Tits are not used. All theorems
retain arbitrary universe `u`, all field and residue characteristics, and the
actual full-star conditions. Independent review and publication are still
required for this contribution and its prerequisites.
