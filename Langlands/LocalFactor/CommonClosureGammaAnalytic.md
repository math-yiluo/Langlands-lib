# Analytic representatives of conditional common-closure gamma

This derived helper connects the actual common-closure gamma value to the
spectral determinant expression. The field and carrier universes remain
independent, with the carrier universe convention of `CommonClosureWeilDeligne.Pair`.
All actions, inertia subgroups, supplied geometric Frobenius lifts, harmonic
data and local-constant assignments are retained.

The actual invariant-quotient correction is analytic at every complex spectral
argument. Its published polynomial expression is composed with the entire
function `exp(-s log q_E)`. The full conditional epsilon is therefore analytic
wherever the ordinary supplied-system Deligne value is analytic. Its
nonvanishing follows from the existing unit-valued codomain.

`gammaExpression` uses this actual full conditional epsilon and the actual
Euler operators of the parameter and its dual. On every point of the published
common regular domain it equals `conditionalGammaValue`. The equality includes
the invariant-quotient correction, and the ratio has orientation
`epsilon(s) D_A(s) / D_dual(1-s)`. The expression is meromorphic wherever the
ordinary Deligne value is analytic.

Under underlying unitarity, each denominator is nonzero on a punctured
neighborhood of every complex center. For the original denominator this is the
published unitary spectral result. For the reflected dual denominator the proof
forms its entire reciprocal object directly: reflection is analytic, and the
nonzero witness is the spectral point `1` before reflection, which corresponds
to `0` after reflection. The identity theorem then gives punctured
nonvanishing. Consequently any complex function agreeing with the conditional
gamma value on all original regular points has the same punctured germ as
`gammaExpression`.

If the ordinary Deligne value is analytic at every real point, the unitary gamma
order theorem applies to that germ. A strictly positive order at a real point
forces that point to be zero. Equality of punctured germs transfers this
conclusion even when the point itself is excluded from the original regular
domain.

The proof is an elementary derivation from the published conditional factor
identities, polynomial analyticity, isolated zeros, and unitary gamma order
helper. Ordinary epsilon analyticity is an explicit remaining premise; the
four local-constant-system relations are not treated as a proved spectral
conductor law. This module supplies no system existence, conductor formula,
arithmetic/automorphic comparison, automorphic positive-form existence or proof
of the full associated-pair induction proposition.
