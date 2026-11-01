# Finite rational coverage of every full affinoid domain

Author: Worker 36.

`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteRationalCoverStatement`
states the finite rational coverage of an arbitrary full represented affinoid
domain. The definition returns `Prop`; it does not prove the covering theorem
or provide a chosen covering as an assumption.

For every complete ultrametric normed field `K : Type u`, every actual
`A : PresentedAffinoidAlgebra K`, and every `U : Domain K A`, the target asks
for a natural number `n`, a family `D : Fin n → RationalChart K A`, and actual
arrows `(D i).toDomain ⟶ U`, such that every point of `U.locus` belongs to
one of the rational loci `(D i).locus`.

Every `D i` is rational over the ambient algebra `A`, rather than merely over
`U.algebra`. It stores finitely many coefficients lifted to the original
weighted Tate algebra, positive real radii, and generation of the unit ideal
by the coefficient classes. Its algebra is the actual closed rational
quotient, and `toDomain` uses the proved full rational representation property.
An arrow `(D i).toDomain ⟶ U` stores a bounded unital homomorphism
`U.algebra → (D i).algebra` whose composite with `U.baseMap` is `(D i).baseMap`.
Its existing `Inclusion.subset` theorem ensures
`(D i).locus ⊆ U.locus`. Together with the point-covering conclusion, these
arrows therefore express exactly a finite union of ambient rational loci.

Including actual arrows does not assume an additional analytic theorem beyond
the finite-union assertion. Once a rational locus is contained in `U.locus`,
`Domain.inclusionOfSubset` constructs its bounded restriction from the full
affinoid-test universal property of `U`, applied to the actual rational
quotient algebra. Conversely every such arrow entails containment.
The finite index is expressed as `Fin n` to avoid an irrelevant choice of
finite index type. The value `n = 0` is permitted. Empty domains and spectra,
zero and nonreduced algebras, trivial valuations, empty coordinate tuples and
arbitrary positive base and rational radii are retained.

The original source is V. G. Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1, printed/PDF p. 9, gives full affinoid-domain representation.
Exercise 2.2.2(ii), p. 9, gives positive-radius rational domains, and
Fact 2.2.5, p. 10, states the Gerritzen–Grauert theorem: each affinoid domain
is a finite union of rational domains. The conclusion here retains precisely
that ambient finite coverage, with its actual bounded restrictions.

The source describes rational coefficients by absence of common spectral
zeros. The Library stores their explicit unit generation. The published
`span_range_eq_top_iff_forall_spectrum_exists_ne_zero` in
`GeneralizedAffinoid.SpectrumIdealCriterionProof` proves the equivalence for
finite coefficient families over the complete coefficient field, including
empty tuples and zero algebras. Coefficients of the quotient have lifts through
the surjective `presentationMap`. Thus the existing chosen rational
presentations express these rational domains without adding a value-group or
strictness condition. The source display in Exercise 2.2.2(ii) contains
inconsistent numerator and arity indices; the imported rational chart uses
one common denominator and one radius for each numerator.

This is a proposition about the Library's category of finite
positive-polyradius quotient presentations, with its full presented-affinoid
tests; no equivalence with a separate abstract Banach-algebra category is
asserted. It supplies no proof of Gerritzen–Grauert, no unrestricted
intersection or saturation construction, and no scalar descent, structure
sheaf, analytic site or cohomology theorem. The strict standard-refinement
theorem in `StrictTestDomain.FiniteRationalRefinementProof` starts with an
already rational covering of the whole strict spectrum; it does not prove
this target for an arbitrary represented affinoid domain.
