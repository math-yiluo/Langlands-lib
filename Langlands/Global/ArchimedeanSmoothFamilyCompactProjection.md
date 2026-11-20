# Compact intertwiner values in a closed span

`SmoothFamily.coefficientIntertwiner` applies the Library's inverse matrix-coefficient average in each smooth slice. For each source vector its value depends continuously on the input family. Averaging a vector in the generated enveloping module stays in that module. Its compact orbit is contained in a finite-dimensional subspace of the module, and the simultaneous average belongs to the closure of that orbit's span, which is already closed.

For a compact intertwiner, summing these averages on the images of the coordinate basis vectors recovers its value. The scalar integrands sum to the value of the intertwiner applied after the source action and its inverse. The normalized compact measure integrates this constant to itself.

The finite-dimensional subspace bounding values of algebraically generated intertwiners is closed, and the inverse image under each coefficient average is closed. Each inverse image contains the generated module, so it contains its closure. Applying the basis sum then gives the same finite-dimensional bound on intertwiners valued in the closure.

This is an internal extension of the Library's `ArchimedeanCompactCoefficientAverage.lean` and `ArchimedeanCompactTypeClosureTransfer.lean`. It serves the passage from finite generation to convolution in Borel–Jacquet, *Automorphic forms and automorphic representations* (1979), §§1.6 (2) and 2.1, printed pp. 191 and 193, PDF pp. 186 and 188.
