# Assembling the archimedean cuspidal block evaluations

`infiniteCompactCoordinates` identifies the actual standard infinite compact group with the indexed product of the orthogonal and unitary matrix groups at all infinite places. The coordinate formulas agree with the real and complex matrices of the adelic element in the mixed coordinates.

The source of `infiniteEvaluation` is the tensor of the real and complex standard modules with the original concatenation order at each place. Its target is the tensor, over those same places, of the block coefficient tensors in the actual cuspidal realizations. The evaluation at an infinite compact point is the indexed tensor of the local evaluations at its compact coordinates.

`infiniteStandardAction` is the right compact action of the actual group, via those coordinates and the local standard actions. `infiniteEvaluation_right` follows from the individual right translation laws and the composition law for indexed tensor maps.

This is an internal assembly of the local evaluations for `CuspidalIsobaricAutomorphyStatement`. Flath (1979), §2, pp. 180–181 (PDF 176–177), gives the tensor product context, and Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the scalar compact model.
