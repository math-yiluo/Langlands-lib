# Ultrametric completion of a seminormed additive group

`Langlands.Analytic.completion_isUltrametricDist` equips the uniform completion
of any ultrametric seminormed additive commutative group with
`IsUltrametricDist`. Its statement and density proof are moved unchanged from
[LaurentGaussField](../Geometry/Analytic/GeneralizedAffinoid/LaurentGaussField.md).

The proof applies `UniformSpace.Completion.induction_on₂` to the closed
inequality `‖x + y‖ ≤ max ‖x‖ ‖y‖`. On the dense original group, the completion
norm and addition formulas reduce it to the given ultrametric inequality.
No nontriviality, completeness or field hypothesis is imposed on the input.

The Laurent-field and completed-tensor constructions both import this single
instance. This extraction adds no mathematical result or extra assumption.
