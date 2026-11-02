# Positive forms on actual CM images of automorphic realizations

This internal construction transports a supplied whole-operator positive
Hermitian form to the existing actual CM image of an automorphic realization.
The CM number field has arbitrary universe, the matrix rank is any natural
number, and the coefficients are complex. CM conjugation acts on function
arguments and leaves complex values unchanged.

For `b : S.UnitaryForm`, `b.complexConj` is a chosen form on
`S.complexConj.Space`. Its value on `f, g` is

`b.inner (S.complexConjEquiv.symm f) (S.complexConjEquiv.symm g)`.

Here `S.complexConjEquiv` is the actual continuous complex-linear equivalence
from the original embedded function space to its CM image. The formula is
pullback by its inverse, so the actual image equivalence preserves the form
exactly. Positivity and definiteness come from the published injective
equivariant pullback construction.

For finite invariance, the construction first retains the original positive
core under precomposition by the actual finite adelic CM automorphism. It
then pulls that form through the inverse finite representation equivalence
of the actual image. The compact construction uses the same core and
underlying inverse map, with the actual automorphism of the standard
infinite compact subgroup. Its invariance therefore proves compact
invariance of this very same form.

For each actual real Lie direction `X`, the published differential covariance
identifies differentiation on the CM image with differentiation on the
original carrier at the transported real direction. The enveloping lift sends
the generator of the complexification of `X` to the generator of the
complexification of `ArchimedeanLieTransport.realLieEquiv ... X`. The shared
`Langlands.Automorphic.inverse_operator` lemma in
[OperatorUnitaryForm](OperatorUnitaryForm.md) derives the inverse operator
covariance from surjectivity and the inverse identities. Applying that covariance under both
arguments of the original form reduces the skew equation to `b.real_skew`
at that real direction. No skew condition for all complex Lie elements is
imposed.

The constructed form proves preservation of
`OperatorRealization.IsUnitarizable`. Applying the construction twice and
using equality of the actual double CM image with the original realization
proves reflection. Quotient induction gives the same equivalence for the
existing whole-operator isomorphism classes. For the existing positive-rank
cuspidal realizations and their classes, the corresponding results retain
the explicit `CompactSpace (AdeleQuotient K)` assumption of those types.
The class result uses the existing forgetful map to whole-operator classes.

The provenance is internal: this pair composes the published positive-form
restriction and pullback operations with the actual finite, compact and
differential CM covariance and the already constructed image/class
involutions. It makes no new identification with original literature.
The initial positive form remains an input. There is no continuity assertion
for the form, invariant integral, Hilbert completion, unitary globalization,
spectral occurrence, contragredient identification or conjugate self-duality
claim.
