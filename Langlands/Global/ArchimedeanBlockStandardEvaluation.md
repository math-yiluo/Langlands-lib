# Normalized evaluation of the real and complex standard tensors

`StandardBlockEvaluation` records the linear tensor evaluation at a compact point together with its normalized parabolic evaluation formula. The scalar formula evaluates the original standard function at the parabolic element times the compact point. The result is the positive local half modulus times the tensor evaluated at the actual block Levi projection.

The real and complex instances use the compact evaluations of the concatenated standard modules. The position character at an included coordinate is the character of its original block. The actual compact diagonal embedding agrees with the embedding used by the real evaluation. Restricting a tensor evaluation to compact block arguments gives the compact evaluation of that tensor. The normalized principal-series comparison then proves the formula for every parabolic argument in both fields.

The two `OfShape` constructions apply these comparisons to any given ordered block shape with the same block ranks. They transport the dependent standard-module and compact types by the supplied rank equalities. This is an internal application of the function-level induction-in-stages comparison in Knapp and Vogan (1995), Chapter XI, (11.196), and the normalized scalar model of Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283).
