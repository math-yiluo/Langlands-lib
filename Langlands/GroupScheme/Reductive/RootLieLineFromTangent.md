# Actual root Lie lines from intrinsic root tangent bounds

This internal construction produces an actual linear trivialization of a
root weight space from a bound on the full intrinsic root tangent.
It also gives a conditional route to these trivializations over arbitrary
fields from two explicit structural propositions. All fields and actual
group schemes remain in arbitrary common universe `u`.

`finrank_weightSpace_eq_one_of_rootTangent_le_one` applies to a smooth
affine group over a field, any supplied split torus mapping to that group,
and an actual root character. The published all-test root tangent
comparison places the original weight space inside the intrinsic tangent
submodule of the actual root functor. The assumed tangent bound therefore
bounds its dimension by one. The weight space is nonzero by actual root
membership and is finite dimensional because the ambient group is smooth
and affine. Its dimension is consequently exactly one.
`rootLieLineOfTangentBound` chooses an actual linear equivalence from the
ground field to that same weight space using the dimension-one
characterization. The chosen coordinates carry no additional normalization.

`rootLieLine_of_dynamicCentralizerReductive` applies the existing
algebraically closed intrinsic root-tangent argument. It supplies the
published proofs `solvableProperFixedPoint`,
`projectiveTorusFixedPointDimension`, and `solvableTorusQuotient` to
`absoluteRootTangent_le_one_of_structuralInputs`. The sole structural
proposition retained as an argument here is
`DynamicCentralizerReductiveStatement`. The actual split maximal torus and
the actual connected reductive group are the objects of that argument.
The tangent-bound construction then gives the original root Lie line.

`rootLieLine_of_twoStructuralInputs` works over an arbitrary field. It
retains `DynamicCentralizerReductiveStatement` and
`MaximalTorusBaseChangeStatement` as explicit hypotheses. Connected
reductivity and splitting persist in the actual scalar extension to the
algebraic closure. The maximal-torus hypothesis is transported by the
supplied maximality theorem, and actual root membership is transported by
the proved root-support comparison. The preceding result gives a line
trivialization of the actual pulled-back weight space.
`weightSpace_line_baseChange_iff` reflects the line to the original field.
Thus no perfectness or characteristic restriction is added.

Worker 1333 authored this derived assembly from the cited imported
constructions and proved comparisons. The two structural proposition
arguments remain obligations; this module proves neither of them and
does not assert unconditional root lines, pinning existence, quasi-split
inner-form existence, or Steinberg quasi-splitness. The last theorem gives
the pointwise conclusion requested by `SplitRootLieLineStatement`, with
these two additional structural hypotheses still explicit.
