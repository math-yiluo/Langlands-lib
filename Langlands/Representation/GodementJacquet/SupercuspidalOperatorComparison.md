# Descending the Fourier-regular operator comparison

This derived helper separates the algebraic comparison argument from the
actual Fourier exchange identity. Its final result assumes that identity
for a supplied comparison family. It proves a scalar comparison under that
explicit hypothesis; it does not assert the hypothesis for Fourier transforms.

For any index type `I` and complex module `V`, the definition
`operatorFamilyLinearCombination A` sends a finitely supported complex
function on `I × V` to the corresponding finite sum of outputs `A(i)v`.
Suppose two operator families `A,D` satisfy
`A(i) * D(j) = D(i) * A(j)` for every pair of indices, and the intersection
of the kernels of the `A(i)` is zero.
`operatorFamilyLinearCombination_ker_le` proves that every finite relation
among the first family's outputs is also a relation among the second
family's outputs. Indeed, applying `A(i)` to the second sum gives `D(i)`
applied to the first sum, which is zero, and the common-kernel condition
forces the second sum to vanish.

If the finite-output map for `A` is surjective,
`operatorFamilyComparison A D` descends the finite-output map for `D`
through the kernel quotient of the finite-output map for `A` and the first
isomorphism theorem. `operatorFamilyComparison_apply_output` states its
defining identity `f(A(i)v) = D(i)v`. The cross identity and output
surjectivity imply `operatorFamilyComparison_commutes`: each `A(i)` commutes
with `f`.

The p-adic part uses every prime, canonical `PadicField.{uF} p`, canonical
topology and normalized absolute value, and a complex representation carrier
in independent universe `uV`. It retains the supplied unitary additive
character, additive Haar measure and self-duality proof.
`fourierRegularMatrixZetaOperator` is the complex-linear restriction of the
existing actual compact matrix zeta operator to the submodule of full-matrix
tests whose original and actual plus Fourier transforms both vanish on
singular matrices. Its evaluation lemma identifies it with the existing
regular-test operator on the underlying test.

In rank `m+1` with `m > 0`, a supercuspidal representation has a
Fourier-regular test with a constant nonzero output on every chosen nonzero
input. Therefore `fourierRegularMatrixZetaOperator_separates` proves the
zero common kernel condition at every complex exponent, without assuming
irreducibility. With irreducibility,
`fourierRegularMatrixZetaOperator_output_surjective` obtains a nonzero input
from irreducibility and uses the existing monomial-output spanning theorem.
Every monomial output lies in the range of the finite-output map because its
integer spectral-power factor is nonzero. Thus the range is the whole carrier.

`intertwining_of_commutes_fourierRegularMatrixZetaOperator` shows that
commutation with every Fourier-regular test operator forces commutation with
the representation. Left translating a test by `a⁻¹` multiplies its operator
by the nonzero determinant weight times `ρ(a)` on the left. Commutation with
that translated operator and the original operator gives
`f(ρ(a)A(Φ)v) = ρ(a)f(A(Φ)v)` after cancelling the determinant weight.
Finite-output surjectivity extends this equality to every vector.

Finally, `exists_scalar_of_fourierRegularMatrixZetaOperator_cross` applies
the general construction with the actual Fourier-regular zeta operators
at a fixed exponent as `A` and an arbitrary supplied family `D`.
Its explicit premise is the cross identity above. The constructed comparison
is an intertwiner by the preceding result; admissibility from supercuspidality
and the published admissible Schur theorem make it scalar. Consequently there
is a complex number `c` such that `D(Φ) = c • A(Φ)` for every Fourier-regular
test. The theorem does not assert that `c` is nonzero or monomial in the
spectral point.

The provenance is internal: finite linear combinations, the kernel quotient
and the first isomorphism theorem are standard module constructions; the
p-adic specialization combines the existing constant-output witnesses,
monomial-output spanning, actual left-translation covariance and admissible
Schur theorem. Worker 200 supplied the corrected cross-operator order used
here. Proving that cross identity for the actual Fourier comparison family,
proving a monomial scalar and extending to arbitrary tests remain separate
obligations of the full functional equation.
