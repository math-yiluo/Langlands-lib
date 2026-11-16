# Completed residue comparison for full affinoid domains

`Langlands.Analytic.PresentedAffinoidAlgebra.DomainCompletedResidueSurjectivityStatement`
is a proposition asserting the following. Let `K : Type u` be a complete
ultrametric normed field, let `A` and `B` be presented affinoid `K`-algebras,
and let `f : BoundedAlgHom K A B` represent a subset `U` of the spectrum of
`A` in the published sense `Represents K f U`. For every spectrum point `y`
of `B`, the actual canonical map

`completedResidueComap K f y : H(comap f y) → H(y)`

is surjective. The ground-field universe is arbitrary. Trivial norms,
arbitrary finite positive polyradii and empty spectra are allowed.

The hypothesis `Represents` includes closedness of `U`, equality of `U`
with the range of the actual spectrum map, and unique bounded factorization
against every presented affinoid test algebra, without a strictness
restriction. The conclusion concerns this particular canonical completed
residue map, rather than existence of an unrelated field isomorphism.
The imported construction already proves it is isometric. Thus the proposed
surjectivity says precisely that this canonical isometric embedding is an
isomorphism of the completed normed residue fields.

## Source correspondence

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
§1.4, printed p. 30, in the paragraph beginning “We remark that with each
point”, describes a field `H(x)` together with a canonical bounded character
from every affinoid domain containing `x`. This character identifies `H(x)`
with the completed residue field calculated in that domain. The same
paragraph states that morphisms induce isometric embeddings of these
fields. Applied to a domain inclusion, both field calculations therefore
identify canonically. The Library's canonical comap is the map characterized
by compatibility with the original algebra evaluations, which is the
compatibility used by those source identifications.

The registered source is `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`;
the retained PDF's zero-based page index is 26 (one-based page 27).

For the full domain meaning, Berkovich, *Spectral theory and analytic geometry
over non-Archimedean fields* (1990), Definition 2.2.1, printed p. 27
(zero-based PDF page 40, one-based page 41), uses bounded maps of affinoid algebras and unique
factorization against all affinoid algebras. It does not restrict to strict
affinoids or nontrivially valued ground fields. The current statement uses
the existing Library version of this property on actual finite
positive-polyradius quotient presentations, and retains its explicit range
clause. Passing from the source's affinoid algebras to these presentations is
part of the formal proof obligation; it is not an additional hypothesis.

The registered 1990 source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
PDF SHA256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

## Status and purpose

This module defines the proposition only. It supplies no proof of domain
residue invariance. A proof must derive surjectivity from the stated full
domain property; the target complete field is not itself presumed to be a
presented affinoid test algebra.

The intended application is to extend a prescribed chart character into
a fixed complete target field uniquely across domain restrictions, then
construct compatible characters on all charts through a point. The present
statement does not assert that all-chart construction or the point axioms
of the analytic étale site.
