# Compact adjoints on the original-order infinite standard tensor

`infiniteStandardTensorLie` applies the specified complexified Lie operator in one place of the infinite standard tensor while keeping the extra tensor factor fixed.

A compact translation conjugates this operator by the local unitary matrix in that place. The compact and Lie covariance law of the local standard module gives the equality in the selected slot. The other slots commute with that operator, and tensoring with the identity on the extra factor preserves the equality.

The adjoint on the actual adelic Lie algebra has the same formula for the real matrix direction inserted at a real or complex place. The proof uses the Library's adjoint formulas for the product of compact factors and identifies those factors with the coordinates of the given infinite compact element.

This is internal to the scalar section comparison for `CuspidalIsobaricAutomorphyStatement`. Getz and Hahn (2024), §4.4, Definition 4.4.6, give the local compact and Lie covariance law. The Lean proof uses the Library's original-order standard actions, actual place adjoint formulas, and the linear map for tensoring an operator with the identity.
