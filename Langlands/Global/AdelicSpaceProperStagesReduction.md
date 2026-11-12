# Reduction of proper adelic stages to three geometric inputs

Authors: Worker 128 and Worker 101.

This derived assembly proves `AdelicSpaceProperStagesStatement` conditional on
three explicit geometric statements in the same arbitrary universe:
`LocalFieldProperPointMapStatement`, `SpaceValuativeExistenceStatement`, and
`ProperSchemeBaseChangeStatement`. The unchanged target is imported from
`AdelicSpaceProperInputsStatement`.

`AdelicSpaceProperStagesReductionStatement` names precisely the implication from
those three statements to `AdelicSpaceProperStagesStatement`, in that order.
It is a proposition definition. The theorem `adelicSpaceProperStagesReduction`
proves this implication by applying `adelicSpaceProperStages_of_inputs`.

For the curve-place statement, the proof introduces exactly its original
parameters: a global function field over a finite constant field, a nonempty
initial level, separated finite-type models, a proper morphism, and any level
containing the initial one. The first component is the actual stage-map
properness supplied by `curvePlaceSpaceStage_isProperMap_of_proper`. The second
component is `curvePlaceSpaceStagePreimage_of_valuative`; properness of the
base-changed morphism is obtained from the explicit scheme-base-change input.
Thus the two components have precisely the actual stage topology and actual
full-adele range-preimage equality required by the published statement.

The number-field proof has the same two components, using the corresponding
number-field lemmas. It retains all infinite places and allows any initial
finite level, including the empty one. The final theorem pairs the two
arithmetic cases. No additional hypothesis is inserted in either published
statement.

The proof route is the composition of the local-to-stage properness reduction
by Worker 101 with the full-level preimage and every-stage transport reductions
by Worker 128. These reductions use the Library's actual ring-point and
base-change constructions. This assembly does not discharge any of the three
geometric inputs and is not an unconditional proof publication of the host
task's target.
