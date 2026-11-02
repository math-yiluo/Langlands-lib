# The positive-radius rational algebra sheaf

Authors: Worker 36 and Worker 74. The imported finite relative-gluing
assembly is adapted from Worker 135's argument, credited in its own pair.

`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.rationalPresheafIsSheaf.{u}`
proves `RationalPresheafSheafStatement.{u}`. For every complete ultrametric
normed field K and presented affinoid base P, the actual
`algebraPresheaf K P` is a Mathlib commutative K-algebra-valued sheaf on
`finiteRationalTopology K P`. The companion `rationalSheaf.{u}` proves
`RationalSheafStatement.{u}`, pairing this result with finite scalar gluing.
Neither closing theorem has a finite-gluing or sheaf premise.

All base polyradii and rational relative radii may be arbitrary positive
real numbers. The actual section algebras are the constructed closed-ideal
weighted Tate quotients. Presheaf arrows are their actual bounded algebra
restrictions after forgetting the norm and chosen presentation.
The target statement pair and every imported definition are unchanged.

## Separation on finite covers

The private conversion is parameterized by `FiniteRationalGluingStatement`;
the closing theorem discharges this parameter with the proved
`finiteRationalGluing`, imported from `GeneralizedAffinoid/FiniteRationalGluingProof`.
That theorem applies the existing unconditional positive-radius
whole-spectrum gluing theorem over the target quotient and transports its
conclusion through the constructed relative comparisons.

`restriction_comp_apply` states composition on actual quotient elements.
The category's arrows are subsingleton: a bounded map out of a rational
quotient is determined by its equation over the fixed base. Thus the two
composites from a chosen intersection to a common target are equal.

For `eq_of_restrictions`, restrictions of a target section form a compatible
tuple by these composition identities. Finite gluing supplies a unique
amalgam. Two target sections with the same restrictions are both that
amalgam, so they are equal. This proves separation using equality of actual
quotient elements.

## Every covering sieve

`rationalUnderlyingIsSheaf` proves the Type-valued compatible-family
condition for the actual presheaf followed by `forget (CommAlgCat K)`.
Start with any covering sieve S on d and a compatible family x indexed by
its arrows. The definition of the finite rational topology supplies a
finite family `f i : D i → d` in S whose loci cover d. Compatibility of x
on the chosen pairwise intersections is exactly the finite-gluing overlap
condition. The analytic theorem produces `a : d.algebra` with the prescribed
section x(f(i)) on every chosen member.

For an arbitrary arrow `g : e → d` in S, the intersections `e.inter (D i)`
cover e: each point of e belongs to d by g and hence to a chosen D(i).
The restrictions of `g.restriction a` and x(g) to these intersections
agree. Composition rewrites the first restriction using the chosen-family
equations for a; compatibility of x gives the second equality.
The separation helper on this intersection cover proves
`g.restriction a = x g`. This proves the amalgam equation on every arrow
of S. Any other sieve amalgam satisfies the chosen finite-family equations,
so finite uniqueness identifies it with a.

The proof uses no nonemptiness premise. For an empty covering family, finite
gluing still supplies the unique actual target element, and the intersection
family remains a cover of every arrow source. The same separation argument
handles empty covering sieves and families.

## Passage to commutative algebras

`rationalPresheafIsSheaf_of_finiteGluing` applies Mathlib's
`isSheaf_iff_isSheaf_of_type` to the carrier-valued result and then
`Presheaf.isSheaf_iff_isSheaf_forget` to the forgetful functor from
commutative K-algebras to types. This functor preserves limits: it is the
composite of the equivalence with commutative rings under K, the under-category
projection, and the commutative-ring carrier functor. Mathlib supplies these
limit properties and reflection of isomorphisms. The result is the categorical
sheaf condition in commutative K-algebras for the actual algebra presheaf.
The closing theorem supplies proved finite gluing to the private conversion;
`rationalSheaf` conjoins the two established assertions.

## Provenance and scope

Worker 36 adapted Worker 74's published
`StrictTestDomain/RationalSheafProof` all-covering-sieve conversion, with
`Restriction` replacing strict locus-inclusion arrows and `algebraPresheaf`
replacing the strict presheaf. Only the actual weighted chart definitions,
map equations, intersections and covers are used. The categorical argument
is derived internally; its analytic input is the proved finite gluing theorem.

The source context is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), registered as `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)-(iii), printed/PDF p.9, give rational
domains and intersections. Fact 2.2.6(i), p.10, gives finite-cover Tate
acyclicity. Exercise 3.2.5(ii)-(iii), p.15, describes affinoid functions and
the structural sheaf for the full G-topology. These passages were read
directly. This proof uses the established quotient gluing theorem without
assuming any source conclusion as a new formal premise.

The arbitrary universe u and the site's field-universe finite-index
convention are retained. Zero and nonreduced quotients, empty numerator
tuples and loci, and trivial scalar valuations remain allowed. The result
is a sheaf in commutative K-algebras on the existing fixed-base finite
rational site, with arbitrary positive base and relative radii. It does
not assert a sheaf in Banach algebras or a gluing norm estimate. The full
analytic G-topology, higher acyclicity, finite-module descent, locally
ringed spaces, analytic atlases and etale or equivariant sites remain
outside this theorem.
