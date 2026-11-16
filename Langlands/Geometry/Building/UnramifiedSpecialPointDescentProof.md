# Proof that special points descend from the unramified building

The theorem `Langlands.Geometry.Building.unramifiedSpecialPointDescent` proves
exactly the published `UnramifiedSpecialPointDescentStatement.{u}` from
[UnramifiedBuildingDescentReduction](UnramifiedBuildingDescentReduction.md),
the Library formulation of KP Proposition 9.9.2. It retains the arbitrary
universe, both characteristics and every published binder and hypothesis.

The implemented proof is the application of
`unramifiedSpecialPointRootJumpReduction` from
[UnramifiedSpecialPointRootJumpReduction](UnramifiedSpecialPointRootJumpReduction.md)
to `unramifiedRootJumpDescent` from
[UnramifiedRootJumpDescentProof](UnramifiedRootJumpDescentProof.md).
The first theorem proves
`UnramifiedRootJumpDescentStatement.{u} → UnramifiedSpecialPointDescentStatement.{u}`.
The second proves its antecedent unconditionally at the same universe.
Their composition is the entire proof in this module.

The reduction converts specialness of the upper building point to apartment
specialness. For each relevant vanishing upper affine root, the root-jump
theorem supplies an actual rational lower root-group point with restricted
valuation zero and the same derivative kernel. The generic geometric result
`isSpecialPoint_of_rootJumpDescent` uses these witnesses to prove specialness
of the chosen lower apartment point. The equality of its root-function family
with the restriction of the fixed upper point identifies the required
valuations. The hypothesis identifying the whole lower apartment carrier is
retained in the exact target, although the reduction only needs the equality
at the chosen points.

This is an internal deduction from the two named Library theorems. Their
paired Markdown describes the geometric reduction and the actual integral
root-specialization and Henselian lifting route. This module introduces no
additional source assertion or geometric construction. Its proof uses no
`UnramifiedBuildingDescentStatement`,
`UnramifiedBuildingDescentReductionStatement`,
`UnramifiedBuildingDescentRemainingReductionStatement`, or result consuming
one of them. The target's defining module is imported through the published
reduction solely for the target and its underlying definitions.
