# Assembly of the quaternionic spin-kernel generator statement

`Langlands.GroupScheme.Quaternionic.SpinKernel.spinKernelGenerator` proves exactly
`Langlands.GroupScheme.Quaternionic.SpinKernel.SpinKernelGeneratorStatement.{u}`,
defined in `Langlands.GroupScheme.Quaternionic.SpinKernelAssembly`, at arbitrary universe `u`.
This is an internal assembly of the quaternionic binary spin comparison, adapted
orthogonal coordinates, and the orthogonal central-cover kernel calculation.

The hypotheses are those of the published statement: a nonarchimedean local field `K`,
a central quaternion division algebra `D`, an involution with three-dimensional symmetric
subspace, a nondegenerate quadratic form of rank four or five and Witt index one, an actual
spin cover, a hyperbolic pair, and arbitrary lifts of its scalar and reduced-norm-one Levi
morphisms. For every coefficient `K`-algebra `A`, the conclusion says that
`z(u) = mu(u) psi(u · 1)` parametrizes the kernel uniquely by `μ₂(A)`.
No characteristic restriction or additional premise is imposed.

The Lean proof supplies the inputs of `kernelGenerator_of_adaptedCoordinates`:

1. `Langlands.LocalField.infinite_of_isNonarchimedeanLocalField` supplies `Infinite K`.
2. `CentralSimple.exists_matrix_chart` gives a chart of `D` over `AlgebraicClosure K`.
   The dimension-four hypothesis and `finrank_eq_matrix_size` force its size to be two.
3. Since the original rank is four or five, it is positive.
   `SplitCoordinates.exists_adaptedCoordinates` therefore gives a full orthogonal chart
   adapted to the chosen original hyperbolic pair. Its all-test Levi formula is exactly
   `IsAdaptedOrthogonalCoordinates` at the first coordinate.
4. `CentralSimpleUnits.degreeTwoNormOneSimplyConnected` supplies the simple-connectedness
   input for the original norm-one group, and the rank hypothesis gives at least three
   orthogonal hyperbolic coordinates.
5. `kernelGenerator_of_adaptedCoordinates` applies the split-spin cocharacter and its
   original binary square-root comparison to the orthogonal kernel reduction, then
   descends the result to `K` and compares it with the supplied Levi lifts.

The coordinate construction and the reduction hold on every relative test scheme.
Thus the final theorem gives the required assertion on all coefficient algebras, including
nonreduced algebras in characteristic two. The original Witt-index hypothesis remains in
the exact target, though this kernel calculation does not need to use it.
