# Conditional construction of the full unramified fixer model

This derived construction assembles the full-model part
of `UnramifiedParahoricModelStatement.{u}`. It assumes five closed statements:
maximal algebraic boundedness of vertex one-stabilizers, finite normal
finite-index approximation by a nonempty finite vertex set, existence of
smooth models of maximal bounded subgroups, smooth binary intersections, and
finite-index enlargement. None of these five statements is proved here.
All five proposition interfaces and every other imported result are published
in the Library.

`IntegralModel.exists_smoothModel_finset_iInf` iterates the supplied binary
intersection theorem by induction on a nonempty finite set. A singleton uses
its given smooth model. The induction step intersects the new member's model
with the induction model. The literal integral-point subgroup of the result
is the finite intersection inside the same original rational-point group.
The nonempty premise avoids requiring a model of the whole rational-point
group.

`exists_smoothVertexModel_of_maximalBounded` first identifies the canonical
integer subring of the valuation relation induced by `fixedFieldValued F`
with the actual `fixedFieldIntegers F`. The proved unramified arithmetic
supplies its DVR and Henselian structures and algebraic closedness of its
residue field. Rewriting this exact subring equality applies the supplied
general maximal-bounded model theorem without changing the generic group
or its rational points.

`exists_smoothFullModel_of_vertexInputs` chooses a finite nonempty vertex
set using the geometric approximation statement. The preceding two lemmas
construct a smooth model of the intersection of its vertex one-stabilizers.
That statement also supplies containment, normality and finite index of
this intersection in the required norm-one pointwise fixer. Substitution
of the exact integral-point equality makes the supplied enlargement
theorem applicable. Its output is a smooth affine flat finite-type model
over the actual unramified integer ring with precisely the required full
fixer as its literal integral-point subgroup.

`exists_relativeComponentModelData_of_vertexInputs` packages that full
model with its actual affine relative identity component using
`IntegralModel.relativeComponentModelDataOfSmooth`. Connected reductivity in the
supplied building datum gives smoothness and connectedness of the original
generic group, hence geometric connectedness. The constructor preserves
the full model and its original generic identification.

`relativeComponentModelDataOfVertexInputs` chooses the compatible full and
neutral model data from this existence result. Its
`relativeComponentModelDataOfVertexInputs_full_integralPoints` theorem is the
corresponding choice specification, so the chosen full model has exactly the
norm-one pointwise fixer as its integral-point subgroup. The data also include
smoothness of both models, connected fibres of the neutral model, and the
actual all-test relative identity-component inclusion.

These are internal consequences of the imported proposition interfaces,
actual integral-model definitions, proved unramified arithmetic and
relative-component constructor. They introduce no new geometric
existence assertion and discharge none of the five input propositions.
They also do not identify the neutral integral-point subgroup with
`E.zeroPoints` intersected with the pointwise fixer. That comparison,
and thus the exact target proof, remains open.
