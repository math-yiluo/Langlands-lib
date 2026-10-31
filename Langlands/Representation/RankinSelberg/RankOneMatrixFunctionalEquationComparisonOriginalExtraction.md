# Original matrix-to-block extraction with the actual averaged coefficient

Worker 396. This is an internal derived interface for the matrix functional
equation comparison. It composes the published box calculation and the literal
original block-zero identification. It asserts no new source transcription.
The field and representation-carrier universes remain independent.

`OriginalMatrixBlockComparison` states equality on a right half-plane between
the shifted matrix integral of a specified actual bi-smooth coefficient and a
specified scalar times the literal original block-zero integral. The first
model vector is fixed. The second vector is the actual canonical constant-one
rank-one vector. The block parameter is exactly `(m+1)-0-1`, the rectangular
measure is `rectangularMeasure nu 0 1`, and the quotient measure is the supplied
`mu`. The definition itself assumes neither compatibility nor convergence.

`originalMatrixBlockComparison_of_eq_on_box` proves that comparison for any
actual coefficient agreeing with the original model function on a box satisfying
`ModelBoxConditions`. It requires smoothness, compatibility of `mu` and the
actual coefficient model's common matrix convergence half-plane. The box
indicator makes the complete matrix integrands equal, including outside the
box. The matrix convergence premise therefore gives integrability for the
box-cutoff model function. `box_comparison_of_integrable` supplies one real
`C > 0` independent of the spectral parameter, and its integral equality
applies on the supplied matrix half-plane. The exact
`unequalRankIntegralAt_rankOne_one` identity replaces the rank-one model integral
by the literal original block integral for this same compatible `mu`. The
resulting complex scalar is the cast of `C`.

`exists_originalMatrixBlockComparison` chooses the actual box and normalized
averaged coefficient through `exists_box_averagedModelCoefficient_eq`, then
applies the preceding theorem. Its conclusion keeps the integer cutoff and
character level, the positive principal level, all `ModelBoxConditions`, the
compact open subgroup and its compactness witness, left invariance of the box
test and determinant norm one on that subgroup, and pointwise equality of the
actual averaged coefficient with the model function on the box. It then returns
the positive real scalar and the original matrix-to-block comparison for that
exact coefficient and test. These choices remain available to a subsequent
Fourier calculation.

No self-duality, irreducibility, finite length, nonzero-functional premise,
extra rank-one convergence, rational continuation or functional equation is
assumed. The supplied additive Haar measure is retained without normalization.
This result proves only the original scalar comparison. A simultaneous genuine
dual comparison with the same coefficient, test and scalar remains a separate
obligation, as does the host task's closed all-rank theorem.
