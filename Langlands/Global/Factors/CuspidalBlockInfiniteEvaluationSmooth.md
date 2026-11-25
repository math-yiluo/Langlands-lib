# Smooth compact evaluation of the infinite standard tensor

`infiniteStandardAction_isFiniteVector` proves compact finiteness for the actual infinite compact action. The orbit of a pure tensor lies in the image of the tensor of the finite-dimensional local orbit spans. Scalar multiples and sums preserve compact finiteness.

`infiniteEvaluationScalarExtension` chooses a scalar function on the mixed matrix space for each source tensor and each linear functional on the coefficient tensor. The extension is smooth near the chosen compact matrix and agrees with the evaluation on every compact point. Locally, each scalar coefficient is a finite sum of fixed left Levi translates of the standard function. The extensions of those translates to the open set of invertible matrices are smooth. The real and complex place projections then give functions of the actual adelic matrix coordinates.

For a fixed local input, the evaluations lie in the image of its finite-dimensional compact orbit span under evaluation at one. The proof extends the coordinate functionals of a finite basis to the full local coefficient space and obtains a smooth extension for each coordinate. Multilinearity gives a finite sum of products of these scalar extensions for a pure infinite tensor. Linearity handles a general tensor.

This is an internal verification of smooth compact slices for `CuspidalIsobaricAutomorphyStatement`. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the scalar compact picture. The Lean proof uses the Library's local block evaluation formulas and their finite-dimensional orbit spans.
