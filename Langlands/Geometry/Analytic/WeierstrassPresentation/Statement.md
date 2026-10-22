# Bounded extension target for the Weierstrass presentation

Author: Worker 36.

`Langlands.Analytic.WeierstrassPresentation.BoundedExtensionStatement`
has three clauses about the actual enlarged Tate quotient and its bounded
base map, constructed in the Definitions module.

First, every point of the new quotient spectrum restricts to the base locus
where the values of the selected f_j are at most one. This is a forward
inclusion; it asserts neither injectivity nor the reverse inclusion.

Second, two bounded K-algebra maps from the new quotient into any commutative
normed K-algebra are equal if their composites with the base map agree.
The target algebra needs neither completeness nor an ultrametric norm for
this uniqueness assertion.

Third, let the target algebra be complete and ultrametric. Every bounded
map from the base quotient for which the images of the projected f_j have
bounded powers extends uniquely to a bounded map from the new quotient.
The power bounds are explicit: for each j there is a positive real constant
bounding the norms of all its natural powers, including exponent zero.
They are not assumed extension maps and are not inferred here from spectral
inequalities. No normalization of the target unit norm or nontriviality of
the target algebra is imposed.

K is a complete ultrametric normed field throughout. K and the target algebra
have independent universes; the two finite variable counts may be zero.
The relation set is arbitrary, and the equations use specified Tate series
whose images lie in the base quotient. The definitions use the closure of
the generated ideal without assuming that all Tate ideals are closed.

This is derived infrastructure for the unit-radius Weierstrass construction
of Berkovich's *Non-archimedean analytic spaces* (Trieste 2009),
Exercise 2.2.2(i), p.9, with the strict quotient conventions of
Definitions 2.1.1-2.1.2, p.7. The bounded-extension context of
Exercise 2.1.5(i), pp.7-8, uses affinoid targets and spectral inequalities.
Here the target may be any commutative complete ultrametric normed algebra,
and explicit power bounds supply the convergent evaluation. This difference
is intentional. The proposition does not identify the spectrum image,
prove presentation independence, or establish the analytic-domain universal
property of Definition 2.2.1, which requires factorization from a condition
on the spectrum image. Those remain separate obligations.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
