# Analytic Weierstrass division and preparation at unit radius

Author: Worker 56.

`RestrictedSeries.WeierstrassStatement A` combines the division and
preparation propositions for actual one-variable restricted series over
`A`. The coefficient ring is a complete, nontrivial, ultrametric normed
commutative ring with multiplicative norm and unit norm one. Its
restricted series carry the constructed Gauss norm.

`DistinguishedDivisionStatement A` says that a distinguished series `f`
of degree `d` divides every series `g` with a unique pair `(q, r)`, where
`q` is a restricted series and `r` is a polynomial of degree less than
`d`. The identity is `g = f*q + r`, using the actual polynomial inclusion,
and both `‖f*q‖` and `‖r‖` are at most `‖g‖`. The use of `Polynomial.degree`
allows the zero remainder even when `d = 0`.

`DistinguishedPreparationStatement A` says that `f` has a unique
factorization `f = e*w`, where `e` is a unit in the restricted-series ring,
and `w` is a monic polynomial of natural degree `d` with all coefficient
norms at most one. The polynomial condition is exactly the unit-radius
Weierstrass-polynomial condition: its leading coefficient has norm one,
and no coefficient has larger norm.

The source is Section 2.2 of the retained fourteen-page notes of part of
Vladimir Berkovich's course, “2. Affinoid algebras.” Division is the
proposition printed as 2.1.1 on page 3, referred to as 2.2.1 on page 4.
The source's isometric direct-sum formulation implies the two stated norm
bounds for division by a distinguished series. Preparation is Proposition
2.2.2, pages 3–4, with the polynomial terminology defined in 2.2.3 on
page 4. The Lean target specializes the positive radius to one. The
nontriviality and norm-one hypotheses make the source's ordinary
nonzero, normalized norm conventions explicit.

These are proposition definitions with no proof imported from the
division or preparation implementation. They assume only coefficient
distinguishedness, not an output quotient, remainder, unit, or factor.
The conjunction is an internal grouping of the two source statements.

Registered source:
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`,
retained at
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The note-taker and publication date are unidentified.
