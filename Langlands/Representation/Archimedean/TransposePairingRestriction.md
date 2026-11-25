# Restriction of inverse-transpose pairings to an algebraic module

This is a derived comparison lemma for the module
formulation of Aizenbud–Gourevitch, *Generalized Harish-Chandra descent and
applications to Gelfand pairs*, arXiv:0803.3395v7, Theorem 8.2.1, p.23.
It formalizes the restriction and differentiation steps described in
[TransposePairingStatement](TransposePairingStatement.md). It does not
construct a globalization, a smooth contragredient, or an ambient pairing.

`matrixExponentialGL` is the ordinary exponential of a real or complex
matrix, as an invertible matrix with inverse the exponential of its
negative. Actual inverse transpose sends this exponential to the
exponential of negative ordinary transpose. The standard embedding of
the unitary group into the invertible matrices intertwines `compactIota`
with the same inverse-transpose automorphism.

`IsDenseWeakGLRealization` concerns a complex linear injection from the
algebraic carrier into a topological complex vector space carrying an
algebraic representation of the actual general linear group. Its image
is dense, it intertwines the compact actions, and its scalar matrix
coefficients have the prescribed derivatives along every matrix
exponential for every continuous complex linear functional. These are
explicit input conditions. No smoothness, topology on the original
carrier, or existence theorem is inferred from the definition.

`restrictRealizationPairing` restricts both arguments of an ambient
complex bilinear form along the linear map. If the ambient form is
separately continuous, density shows that its restriction is nonzero
whenever it is nonzero: apply equality of continuous scalar functions
on a dense set once in each argument.

For invariance, assume the ambient form satisfies
`B(R(g)y, R(transpose(g⁻¹))x) = B(y,x)`. Compact invariance follows by
intertwining the compact embedding. With `g = exp(tX)`, rewrite group
invariance as
`B(R(exp(tX))y,x) = B(y,R(exp(t·transpose(X)))x)`.
Only one argument varies on each side. The weak derivative comparisons
and uniqueness of the scalar derivative give
`B(dR(X)y,x) = B(y,dR(transpose(X))x)`.
Bilinearity turns this into the required sum with negative transpose.
Tensor-product induction extends the formula to the whole complexified
real matrix Lie algebra, including at complex places.

The final theorem concludes precisely `HasNonzeroTransposeGKPairing`
from these ambient inputs. It is a conditional comparison result, and
leaves their construction and the exact unconditional real/complex
existence statement to further work. The ambient space has an arbitrary
topology; separate continuity and scalar differentiation are sufficient
for the argument, so the lemma also applies to a Fréchet smooth
realization without assuming that its topology comes from a norm.
