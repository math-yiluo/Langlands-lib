# Finite adelic evaluation in the Levi block order

`blockEvaluation` evaluates the actual restricted tensor of normalized local inducing sections at a finite adelic matrix. It expresses the value in the indexed tensor of restricted coefficients of the Levi blocks. The construction composes pointwise evaluation with the equivalence for the normalized parabolic action.

`blockEvaluation_right` gives the right translation law. `blockEvaluation_parabolic` gives the left parabolic law, with the actual adelic half character and the finite adelic action of each projected Levi block.

`blockEvaluation_compact_injective` proves that the integral compact arguments detect every source vector. The block references are nonzero outside the exceptional set, so the tensor of those references is nonzero by testing it with a product of dual functionals. The actual compact coordinates supply every tuple of integral local arguments. The Library's restricted tensor separation theorem then gives injectivity.

This is an internal assembly toward `CuspidalIsobaricAutomorphyStatement` (automorphy of isobaric sums of cuspidal representations at every place, Getz–Hahn Theorem 10.7.5). Flath (1979), §2, pp. 180–181 (PDF 176–177), supplies the restricted tensor setting. The Lean proof uses the Library's pointwise evaluation, parabolic coefficient equivalence and compact evaluation separation.
