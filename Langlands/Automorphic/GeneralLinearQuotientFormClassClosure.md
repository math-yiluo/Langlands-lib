# Invariant Hilbert closure of represented form classes

`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearQuotientFormClassClosureStatement`
and its proof `generalLinearQuotientFormClassClosure` concern the original
positive-central rational quotient of `GL_{r+1}` and its bounded right action.
With the split-centre, right Haar invariance and compact additive adele quotient
hypotheses, let `R` be any operator realization and `j : R.Space →ₗ[ℂ] L²` a
map supplying the actual form class for every realized vector. Then the
closure of `range j` in quotient `L²` is invariant under the entire adelic
right action. Neither cuspidality nor irreducibility of `R` is required.

## Implemented proof

First the finite adelic and standard archimedean compact actions commute with
`j`. The form class relation takes a right translate to the original right
translate on quotient `L²`. The realized functions of the finite and compact
operators are those pointwise translates; uniqueness of their classes gives
the two identities.

Next fix a bounded functional annihilating `range j`. For a realized vector,
its scalar archimedean orbit coefficient is smooth and its enveloping
operators act by taking the coefficient of the enveloping derivative of that
vector, by `generalLinearQuotientOrbitCoefficients`. This intertwines the
centre actions. The compact identity and the group law intertwine compact
translation of the coefficient, so compact and centre finiteness transfer
from the realized form to the coefficient; compact-group finiteness gives
the corresponding differential finiteness. The Library's jointly finite
analyticity theorem makes the coefficient analytic in the matrix chart.

Each connected component contains a standard compact element. At that
element all enveloping derivatives of the scalar coefficient vanish: each is
the functional applied to the class of a compact translate of a differentiated
realized vector. By the enveloping jet comparison and analytic uniqueness on
the component, the coefficient vanishes everywhere. The continuous complex
annihilator criterion now places all archimedean translates of each class in
the closure. Finite translates already lie in the original class image and
both invariances extend to its closure by continuity of the bounded actions.
Factoring an arbitrary adelic point into its two coordinates finishes.

## Provenance and scope

This is a derived ingredient of the passage between operator realizations
and Hilbert summands, in the context of Getz–Hahn, *An Introduction to
Automorphic Representations*, Springer GTM 300 (2024), Theorem 9.7.3,
pp. 265–267 (PDF pp. 277–279). It applies the Library's scalar analytic
annihilator argument to the actual positive quotient through the compact
reproducing kernel comparison, independently of the determinant-band model.
It proves invariance of a given class image's closure, not density of
stable form classes, joint admissibility, or the algebraic irreducibility
of the forms attached to an irreducible Hilbert summand.
