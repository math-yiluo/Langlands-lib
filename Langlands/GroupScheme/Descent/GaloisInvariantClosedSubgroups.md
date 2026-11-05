# Closed-subgroup descent over arbitrary Galois extensions

For an affine group scheme over a field, this internal construction descends
the full defining ideal of a represented closed subgroup of its scalar
extension. The extension may have infinite degree. The input is invariance of
the actual subgroup functor on every relative test scheme under every
canonical Galois translate. The construction `idealSheafDescent` supplies an
actual ideal sheaf on the original affine group whose pullback is the given
closed subgroup's defining ideal.
The theorem `overlap_range_eq` converts that ideal equality to equality of
the two actual ranges on the full fpqc overlap. The theorem `exists_descent`
then produces a ground-field affine group, a closed inclusion in the original
ambient group, and a source isomorphism recovering the prescribed inclusion
exactly after scalar extension.

Over a finite ground field, `idealSheafDescentOfFrobenius` needs only equality
of the original all-test range with the range of its canonical arithmetic
Frobenius translate. It assumes the extension is Galois, but imposes no finite
degree or finite presentation on the closed subgroup.
The companion theorems `overlap_range_eq_of_frobenius` and
`exists_descent_of_frobenius` provide the corresponding full overlap equality
and effective closed-subgroup descent.

The proof first uses equality of represented closed-subgroup images to build
the actual source comparison isomorphism and its semilinear self-map. This
intertwines the inclusion and ambient coefficient conjugation. Passing to
global sections makes the full coordinate kernel stable under that coefficient
automorphism. The already published tensor-coordinate square and Galois-stable
ideal-sheaf descent then supply the ideal sheaf.

For the Frobenius variant, choose any basis of the original affine algebra.
Each tensor has only finitely many nonzero coefficients. Finite-set Frobenius
approximation supplies a power agreeing with any prescribed automorphism on
these coefficients. Induction gives ideal stability under every nonnegative
Frobenius power, hence under every coefficient automorphism. This argument
uses no finite field of definition for the subgroup.

Worker 1611 derived the generalization using the published infinite-Galois
ideal descent of `GaloisIdealDescent`, the tensor-coordinate bridge and radical
source-intertwining proof of `Descent.RadicalTensorIdeal` (Worker 1370), and the
ideal-sheaf adapter of `Descent.RadicalIdealSheaf` (Worker 1359). The latter
proofs are generalized here by replacing the radical-specific invariance
result with the explicitly supplied equality of closed-subgroup images.
This is a supporting descent result; it does not produce a Frobenius-invariant
Borel or prove finite-field quasi-splitness or the host solvability target.
