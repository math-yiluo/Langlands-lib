# Conjugation pairing and central descent

This internal construction realizes the bilinear integral in Waldspurger,
*La formule de Plancherel* (2003), Proposition VIII.3.1, printed p.323
(PDF p.89), and its central quotient in Corollary VIII.3.2, printed pp.326–327
(PDF pp.92–93). The registered source is `waldspurger-2003-plancherel`.
There is no complex conjugation on the second function.

For a group with a measurable space, `conjugationIntegrand f₁ f₂ h g` is
`f₁(h g h⁻¹) f₂(g)`, and `conjugationPairing μ f₁ f₂ h` is its complex
Bochner integral with respect to the displayed measure. This is a totalized
set-theoretic definition. It proves neither absolute convergence nor
measurability of the function of `h`. First and second variable additivity
require explicit integrability of both summands at that `h`. The two
scalar formulas use the unconditional constant multiplication identity
for total Bochner integrals. Together these formulas give bilinearity
where the relevant inner integrals converge; no unconditional bilinear
map on arbitrary functions is asserted.

For any actual central subgroup `A`, multiplying `h` on the left by an
element of `A` leaves `h g h⁻¹` unchanged. The implementation proves this
pointwise equality before passing to integrals. `leftConjugationPairing`
uses the existing `descend` on the genuine coset type `LeftQuotient A`.
The representative evaluation, evaluation at `Quotient.out`, and
independence of any two representatives of a left coset follow without
an integrability or decay hypothesis.

For a topological group and a normal central subgroup, the function
`rightConjugationPairing` on `Γ / A` is the left pairing composed with the
inverse of `normalLeftQuotientHomeomorph A`. The comparison and evaluation
laws use the same group representative. Both quotient measurable spaces
are explicitly assumed to be their Borel spaces. The measure
`conjugationRightQuotientMeasure A ν` is exactly the pushforward of the
left-quotient measure `ν` by this homeomorphism. The proved integrability
equivalence is an equivalence of `MeasureTheory.Integrable` assertions,
including a.e. strong measurability. The total integrals also agree.
These transport laws do not establish either integrability assertion.

On the actual rational points of an affine locally finite type group
scheme over an arbitrary nonarchimedean local field, the canonical
rational-point topological group and Borel instances are used.
`rationalConjugationPairing hKc hPK ρ μ` specializes the construction to
the published `RationalSchwartzSpace`, retaining its compact open subgroup,
Iwasawa pair and matrix representation. `rationalLeftConjugationPairing`
uses the image `(rationalPoints.map s).range` of an actual split component
`s : T → G`. Its centrality is deduced from `IsSplitComponent s`, and
`rationalSplitCenter_normal` proves normality from that centrality. Thus
the generic right-quotient construction applies to exactly this subgroup.
There is no characteristic, splitness, quasi-splitness or positive-rank
restriction.

The elementary constructions use no Haar normalization. In applications
to VIII.3.2, one must separately display group and central Haar measures
`μG`, `μA`, and a left-quotient Borel measure `ν` satisfying the existing
`Langlands.QuotientIntegration.IsCompatible A μG μA ν` (the Weil integral
formula and right invariance). Its right-quotient realization is the
pushforward just defined. This compatibility is distinct from the
Library's compatibility along the open common norm-kernel subgroup.
No compatibility, inner convergence, quotient convergence or analytic
measurability is inferred from central descent. The closed VIII.3 targets
are separate statements, to conclude the analytic properties.
