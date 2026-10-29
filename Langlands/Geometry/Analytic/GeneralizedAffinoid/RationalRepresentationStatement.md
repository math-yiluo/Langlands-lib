# Rational representation against all presented affinoid tests

Worker 56 defines
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalRepresentationStatement`.
This is a proposition definition. The module does not prove it or construct a
domain by assuming it.

## Actual input algebras and rational charts

The proposition quantifies over `K : Type u` with `NormedField K`,
`IsUltrametricDist K` and `CompleteSpace K`, in that order. The valuation may
be trivial. It then quantifies over every
`A : PresentedAffinoidAlgebra K` and every `d : RationalChart K A`.

The imported presentation is an actual quotient of a finite weighted Tate
algebra by a closed ideal, with its quotient norm and proved completeness.
Its finite presentation radii may be any strictly positive real numbers.
The imported rational chart stores a natural number `d.arity`, a strictly
positive radius for each new variable, scalar-series representatives of one
denominator and the numerator tuple, and `d.generates`. That last field says
that the actual denominator and numerator classes in `A` span the unit ideal.
It supplies no factorization or spectral conclusion.

The existing `d.algebra` is the actual enlarged weighted Tate quotient: the
old ideal and the equations `g * Y_j - f_j` generate the ideal whose closure
is divided out. The map `d.baseMap : BoundedAlgHom K A d.algebra` is the
constructed structural map. The set `d.locus` consists of actual bounded
multiplicative seminorms `x` on `A` satisfying
`x(f_j) ≤ d.radii j * x(g)` for each `j`. All coefficients in this formula
are their actual classes in `A`.

## Exact conclusion

The proposition is precisely `Represents K d.baseMap d.locus` for every
such input. Expanding the already published `Represents`, its conclusion
has three clauses:

1. `d.locus` is closed in `BanachSpectrum A`.
2. The range of the actual spectrum comap along `d.baseMap` is exactly
   `d.locus`.
3. For every `R : PresentedAffinoidAlgebra K` and every bounded
   `K`-algebra homomorphism `φ : A → R` whose spectrum image lies in
   `d.locus`, there is exactly one bounded `K`-algebra homomorphism
   `ψ : d.algebra → R` with `ψ.comp d.baseMap = φ`.

Here image containment means that for every `x : BanachSpectrum R`, its
actual seminorm comap along `φ` belongs to `d.locus`. Both the base and
the test presentations have arbitrary strictly positive radii. The test
family is the whole category of presented affinoids constructed in the
Library; a comparison with a separately defined abstract affinoid category
is not asserted. The statement uses the same universe `u` for the field,
base presentation and test presentations.

The maps may have any positive linear norm bound; they need not be
contractions. The conclusion's existence and uniqueness concern the
actual maps, without a chosen extension operator. No inverse denominator,
fraction solution, coordinate bound, monomial bound, spectral criterion,
or representation certificate is an extra input.

Zero presentation variables, an empty numerator tuple, nilpotents and
zero quotients are allowed. For an empty numerator tuple, `d.generates`
requires the denominator class alone to generate the unit ideal, while
the inequality locus is the whole spectrum. No nonzero-algebra or
nonempty-locus hypothesis is added.

## Source and derived presentation formulation

The registered original is V. G. Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed and PDF page numbers coincide.

Definition 2.1.11, p.8, defines affinoid spaces by reversing the category
of affinoid algebras and bounded homomorphisms. Definition 2.2.1, p.9,
requires a closed subset, exact structural image and unique factorization
for every affinoid map with image in that subset. These are precisely the
three clauses of the imported representation predicate in the constructed
presentation category.

Exercise 2.2.2(ii), p.9, states that the positive-radius rational inequality
set is an affinoid domain, represented by adjoining variables with equations
`g * Y_j - f_j`. Its hypothesis is that the denominator and numerator
classes have no common spectrum zero. The present formulation uses the
chart's algebraic unit-generation hypothesis. Unit generation implies
that source hypothesis: a common zero would put the generated unit ideal
in the proper kernel of a normalized spectrum point. The published
`RationalPresentation.denominator_ne_zero` implements the corresponding
argument on the rational locus. No converse from absence of common zeros
to unit generation is assumed by this statement. The formulation is
therefore recorded as derived, rather than a verbatim transcription.

The Library construction writes the relative quotient in the existing
absolute presentation by appending its new variables and relations. This
statement uses that actual closed quotient and the existing actual base
map; it does not assume an abstract relative Tate algebra or an
identification with one.

The existing rational spectrum homeomorphism and bounded extension from
explicit bounded fraction solutions are useful prerequisites. They do
not alone prove clause 3 from only the image hypothesis. The strict-test
statement in
`Langlands.Geometry.Analytic.StrictTestDomain.RationalRepresentationStatement`
concerns different presentations and tests and is not a proof of the
present statement. Generalized spectral ideal and power criteria may be
used in a later proof to derive the missing fraction bounds.

This module supplies none of that proof, a rational chart-to-domain
construction, an equivalence of domain categories, a structure sheaf,
an analytic atlas, an etale site or an equivariant site.
