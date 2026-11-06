# Polynomial domination of full adelic representation heights

`Langlands.Global.RepresentationGrowth.ClosedImmersionAdelicHeightDominationStatement`
is a proposition target. For every number field `F` in an arbitrary universe,
every group scheme `G` over `Spec F`, positive natural ranks `N` and `M`, and
actual matrix representations

```text
rho   : G -> GL_N,
sigma : G -> GL_M,
```

it asserts that a scheme-theoretic closed immersion `rho` gives a real `C >= 1`
and a natural exponent `e` such that, for every actual full adelic point `g`,

```text
adelicHeight F G sigma g <= C * (adelicHeight F G rho g)^e.
```

The constant and exponent precede the point quantifier. The representation
`sigma` need not be faithful or a closed immersion. No reductivity, smoothness,
connectedness, splitness or separately supplied local bound is assumed.
Closedness is the existing `GroupScheme.IsClosedSubgroup rho`; injectivity on
rational or adelic points alone is not its meaning. Since the target of `rho`
is affine, a closed immersion also makes its source affine.

## The fixed height

Both sides use exactly `RepresentationGrowth.adelicHeight`, defined in
`AdelicRepresentationHeight`. This is the product over the infinite places `v`
of `(rank * localMaximum v)^v.mult`, multiplied by the finite product over all
finite places of `localMaximum v`. Each local maximum takes all matrix entries
and all inverse-matrix entries. The finite places have their actual normalized
completion norms. The infinite multiplicity counts a complex place twice.
There is no change to the representation, carrier or local norm in this target.

The existing height construction proves that these scaled local factors are
at least one for positive rank and that the finite local factors equal one
outside a finite set. Its exact unscaled product, `adelicSourceNorm`, differs
by the fixed scalar `rank ^ (sum v, v.mult)`. The positive-rank hypotheses here
retain those facts. In contrast, the earlier
`ClosedImmersionHeightDominationStatement` controls the mixed-space height on
infinite adelic points and includes rank zero. That earlier assertion alone
does not prove this full adelic bound.

## Source and derivation

The motivation is Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), equations (6.3)–(6.4), printed pp.158–159
(PDF pp.172–173), equations (6.7)–(6.8) and Definition 6.3.1, printed
pp.161–162 (PDF pp.175–176), and Exercise 6.1, printed pp.179–180
(PDF pp.193–194). The exercise compares the product norms from two faithful
representations of a reductive group over a global field for any set of places,
including the set of all places. It asks for a positive constant and a real
exponent greater than one and then for independence of moderate and uniform
moderate growth. The complete retained author errata, especially Chapter 6
on p.2, makes no correction to these formulas or Exercise 6.1.

This target is an internally derived coordinate-algebra generalization over
number fields, for the Library's dimension-scaled full product. It is not a
literal transcription of the exercise's hypotheses or exponent convention.
The existing theorem `exists_coordinate_polynomial` in
`RepresentationHeightDominationProof` gives, for each entry and inverse entry
of `sigma`, a fixed polynomial over `F` in the entries and inverse entries of
`rho`, valid at every affine algebra point. Thus it applies at the full adele
algebra and at every completion. One possible proof route is to choose a common
degree for the finite family of coordinate polynomials. At each finite place,
the ultrametric inequality bounds their evaluations by a coefficient bound
times the controlling local factor to that degree. A fixed finite family of
coefficients is integral at almost every finite place, so these coefficient
bounds can be chosen to equal one there. At the finitely many infinite places,
ordinary polynomial estimates and the dimension scaling give fixed constants.
Multiplying the estimates, with the existing multiplicities and finite-support
laws, would give the stated single constant and exponent. These local estimates
and their assembly remain proof obligations.

## Boundary

This file defines only the proposition; it proves no domination inequality.
Applying a future proof in both directions to two closed embeddings would
support independence of the existing full adelic moderate-growth conditions.
For uniform growth, the comparison constants and exponent would have to remain
independent of the enveloping derivative. Neither consequence is exported here.
No properness, reduction theory, finite volume, parabolic classification,
cuspidality or square-integrability assertion is made.
