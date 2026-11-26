# Orthogonal left convolution and polynomial degrees

`continuousDegree n N` is the space of continuous functions on \(O(n)\) whose underlying functions belong to `RealKTypeCount.degreeLE n N`. It is finite-dimensional and therefore closed for the supremum norm.

`leftConvolution` is the bounded operator \(f\mapsto w*f\) obtained by averaging the left translates \(k\mapsto f(y^{-1}k)\) against a continuous weight \(w(y)\). It commutes with right translation. Under left invariance and inversion invariance of Haar measure the same operator has the pointwise formula

\[
(w*f)(k)=\int_{O(n)} f(y)w(ky^{-1})\,dy .
\]

`OrthogonalConvolutionDegreeStatement` gives two bounds for a normalized Haar measure. If the input lies in degree at most \(N\), its left translates remain in that degree, so the integral lies there. If the kernel lies in degree at most \(N\), the second formula expresses the output as an integral of right translates of the kernel, all in degree at most \(N\). Both arguments use closedness of the degree subspace and closure under Bochner integration.

These bounds let a polynomial approximate identity produce a prescribed degree cutoff while preserving each fixed degree subspace.
