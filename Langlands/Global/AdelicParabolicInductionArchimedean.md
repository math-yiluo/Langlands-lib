# Archimedean actions on smooth adelic block sections

The existing normalized space `AdelicParabolicInduction.SmoothSections`
consists of covariant sections with smooth infinite slices and a common open
finite stabilizer. `compactRepresentation` restricts its right action along
the standard infinite compact subgroup of the adelic matrix group.
`evaluate_compactRepresentation` gives the resulting pointwise translation.

Assume that each fixed normalized parabolic operator
`inducingRepresentation F B σ p` is continuous on the normed coefficient
space. Under this hypothesis `realLieAction` acts on the same section space.
At an adelic point with infinite and finite parts \((a,b)\), the differential
in direction \(X\) applies `vectorSmoothDifferential F n X` to the smooth
slice at \(b\) and evaluates it at \(a\). The evaluation formula is
`evaluate_sectionDifferential`. For any supplied real-parameter curve through
the identity with matrix tangent \(X\), `evaluate_realLieAction_hasDerivAt`
identifies this value with the derivative of the section along adelic right
translation by that curve.

For covariance, write a parabolic element \(p\) in its infinite and finite
coordinates \((p_\infty,p_f)\). The section identity relates the slice at
\(p_f b\), pulled back by left multiplication by \(p_\infty\), to the slice
at \(b\) postcomposed with the fixed normalized coefficient operator.
Right differentiation commutes with both operations. Each differentiated
slice is smooth. Right translation by a finite element only shifts the
slice index, so differentiation commutes with this translation and preserves
the original open finite stabilizer.

The real Lie identities follow slice by slice from the identities for
normed vector functions. `complexLieAction` extends the action complex
linearly. Its bracket identity follows by tensor induction, with the
pure-tensor case given by the real Lie bracket and bilinearity of the
endomorphism commutator. Mathlib's universal property then constructs
`envelopingAction`, whose real generators recover `realLieAction`.

This is an internal construction on the actual sections of
[`AdelicParabolicInduction`](AdelicParabolicInduction.md). It uses
[`ArchimedeanVectorDifferential`](ArchimedeanVectorDifferential.md)
for the two chain rules and the real Lie action. The complexification
follows the scalar construction in
[`ArchimedeanEnvelopingAction`](ArchimedeanEnvelopingAction.md).
The construction provides the archimedean operators for comparing the
global constant-term realization with normalized smooth induction. The
normed coefficient space, Levi action and continuity of its fixed
normalized parabolic operators are inputs.
