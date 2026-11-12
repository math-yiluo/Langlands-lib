# Original fixed-base coordinates of curve-place algebraic-space stages

For a finite field `k` and a global function field `F` over `k` with its
specified rational-function-field algebra structure, let `S` be a nonempty
finite set of curve places of `F` and let `T` be an enlarged finite support
containing `S`. For a separated finite-type algebraic space `X` over the
original S-integers, `AdelicSpaceStageCoordinates.curveStageHomeomorph`
identifies the `T`-stage points with the product of `X`'s points over all
original completed-field and completed-integer factors of the `T`-level.

The source is the defined `curvePlaceSpaceStageTopology`. Each target
factor has the field-valued topology through its original inclusion in the
completed field, restricting the coefficient action from T-integers to the
original S-integers. The construction introduces the corresponding
restricted coefficient action on the completed fields and preserves the
published fixed-base factor algebra structures.

The implemented proof composes the defining stage equivalence with the
coordinate homeomorphism on the base-changed model and the product of
`fieldValuedBaseChangeHomeomorph`. The published curve-place level point
bijection supplies the middle equivalence; base change preserves the
separatedness and finite type it needs. The component formula follows by
coefficient naturality of `baseChangeRingPointsEquiv` and cancellation of
the stage equivalence. Its coefficient map is the original product-level
projection, expressed as evaluation after the published fixed-base level
factor algebra equivalence.

This is internal composition of published level bijections and base-change
topology identities. It imposes no separability hypothesis and does not
compare different global fields or prove the adelic Weil restriction
endpoint. It complements the number-field construction and generic
field-valued base-change homeomorphism in `AdelicSpaceStageCoordinates`.
