# Actual Galois action on Harris scheme cocharacters

This module is an internal derivation from the already constructed
rational Harris group, its iterated complex pullback, and the generic
scheme-cocharacter transport in `GroupScheme.CocharacterTransport`.
The existing Harris and Kottwitz cocharacter conventions are retained;
no new literature convention, matrix chart, or reflex-field assertion
is introduced.

## Base maps

The abbreviation `rationalComplexBaseMap` is the actual spectrum map
Spec ℂ→Spec ℚ induced by the usual scalar inclusion. The theorem
`rationalComplexBaseMap_tower` identifies it with the composite through
Spec ℝ. The proof uses contravariant spectrum functoriality and equality
of the resulting rational ring homomorphisms.

For s∈Aut(ℂ/ℚ), `complexGaloisBaseMap s` is Spec(s). The theorem
`complexGaloisBaseMap_over` proves that it is over Spec ℚ using the
algebra-homomorphism scalar compatibility of s.
`complexGaloisBaseMap_one` and `complexGaloisBaseMap_mul` prove

\[
a_1=\mathrm{id},\qquad a_{st}=a_s\mathbin{\gg}a_t,
\]

where (st)(z)=s(t(z)). This is the geometric composition order supplied
by the contravariant spectrum functor. No topology on Aut(ℂ/ℚ) is used.

## Direct and iterated scalar extension

Retain the hypotheses of `CentralSimpleUnitaryData`: E is totally real,
K/E is a totally complex quadratic extension, and A carries the compatible
E-, K- and rational-algebra structures and scalar towers used for the
rational Harris group. Let D be the central simple unitary datum.

The actual cocharacter target `D.complexRationalGroupScheme` was
constructed by successive pullback along ℚ→ℝ→ℂ. The definition
`D.complexDirectGroupSchemeIso` identifies it with the direct pullback
`D.rationalBaseChange rationalComplexBaseMap`. It composes the inverse
canonical pullback-composition isomorphism with the equality isomorphism
from the scalar-tower base-map identity. Thus the change of model is an
actual isomorphism of complex group schemes.

## Galois transport and its action laws

Given any actual complex cocharacter χ with this iterated target,
`D.galoisCocharacter s χ` first transfers χ to the direct rational
pullback using `complexDirectGroupSchemeIso.hom`, applies generic
transport along Spec(s), and returns using the inverse comparison.
The definition therefore constructs an actual group-scheme morphism
Gm_C→D.complexRationalGroupScheme.

The theorem `galoisCocharacter_comparison` cancels the final inverse
comparison and identifies this construction in the direct pullback
model. The generic theorem `transportCocharacter_points` supplies the
all-test-scheme evaluation formula in that model: change the test
scheme's complex structural map by Spec(s), preserve the underlying
unit, evaluate the original cocharacter, and compare the rational
points by the identity map of underlying schemes.

The theorems `galoisCocharacter_one` and `galoisCocharacter_mul` prove

\[
{}^1\chi=\chi,\qquad {}^{st}\chi={}^s({}^t\chi).
\]

They follow from generic identity/composition laws, the spectrum-map
identities above, and cancellation of the direct/iterated comparison.
The definition `galoisCocharacterEquiv s` packages transport as a
permutation of the set of actual scheme cocharacters; its inverse is
transport by s inverse. The definition `D.galoisCocharacterAction` is
the resulting group homomorphism from Aut(ℂ/ℚ) into that permutation
group. This acts on the full morphism set Gm_C→D.complexRationalGroupScheme,
so the previously constructed Harris and Kottwitz cocharacters are
within its domain without additional chart hypotheses.

## Canonical rational point comparison and scope

The definition `D.complexRationalPointsEquiv` identifies actual complex
base points of the iterated group with actual complex points of
`D.rationalGroupScheme` over Spec ℚ. It uses the point map of
`complexDirectGroupSchemeIso`, then the generic pullback base-point
equivalence. This comparison is multiplicative and constructed without
choosing matrix charts.

This module establishes the actual scheme-cocharacter action and its
all-test-scheme interpretation through the generic transport theorem.
It does not yet prove the explicit field-point formula
s(χ(s⁻¹(u))) under `complexRationalPointsEquiv`, compare it with
`complexPointGaloisAction`, compute embedding-factor permutations or
matrix weights, or identify the cocharacter-conjugacy stabilizer with
the previously defined reflex stabilizer. Those are further comparison
obligations.
