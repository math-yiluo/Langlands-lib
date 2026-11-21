# Infinite standard tensor Lie action in compact directions

`infiniteStandardLocalLie` is the real or complex original-order standard Lie action at the chosen place. `infiniteStandardLieAt` acts in that place's slot of the infinite tensor. A local compact point inserted in the full infinite compact group acts in the same slot.

`unitaryExpCurve` is the matrix exponential of a real multiple of a skew-adjoint matrix. Its entries have the given derivative at zero, and the corresponding one-place inclusion has that tangent in the mixed adelic chart. The compact derivative law of the standard module gives the derivative in the local slot. Scalar differentiation of a one-slot tensor then gives the derivative for the standard tensor. An additional tensor factor with trivial compact action remains fixed in this argument.

For each real or complex skew-adjoint direction, a compact intertwiner from that tensor source to the smooth scalar sections intertwines the prescribed local Lie operator with the actual adelic section differential. The proof compares derivatives of the two scalar evaluations along the same compact curve.

This is internal to the inducing model for Task 6553. Getz and Hahn (2024), §4.4, Definition 4.4.6, give the compact differentiation law, and §10.1, pp. 270–271 (PDF 282–283), give the scalar compact model. The Lean proof uses the Library's standard module compact derivative law and actual adelic compact inclusions.
