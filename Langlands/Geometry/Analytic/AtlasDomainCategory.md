# The actual category of local full domains in arbitrary affinoid atlases

`LocalDomain a` consists of an original chart index and an actual full
affinoid-domain representation over its algebra. The atlas is arbitrary,
over a complete ultrametric normed field. There is no directedness or greatest
chart premise. Distinct original charts or presentations remain distinct objects.

Each object retains its actual finite positive-polyradius quotient algebra,
ambient subset and continuous map from its spectrum. The exact original
spectrum image proves `range_ambientMap`. The original chart embedding and
proved full-domain spectrum embedding prove `isEmbedding_ambientMap`.
`locusHomeomorph` therefore identifies the actual spectrum with its ambient
subspace locus, and that locus is compact.

`Inclusion` stores ambient containment and an actual bounded algebra restriction,
with its structural equations over every original chart containing both local
images. `Inclusion.restriction_eq` applies the equation at the target's original
chart, recovers its original domain base map and uses full-test uniqueness to
identify the entire bounded map with the constructed unrestricted restriction.
Thus thinness is proved for these actual maps; arrows are not defined as mere
subset containments. `Inclusion.ofSubset` constructs an arrow for every ambient
containment, including its complete bounded map and all structural equations.
Composition stores the actual contravariant composite map and proves its
structural equations using the two original equations. Bounded identities
and composition give the category laws.

Every arrow has its continuous actual spectrum map and ambient locus inclusion.
The original bounded restriction chart theorem proves ambient naturality and
naturality of the spectrum-to-locus homeomorphisms. `Inclusion.represents`
retains full representation of the literal relative ambient subset in the
target spectrum against every presented affinoid test.

`toAffinoidSpace`, `toTopologicalSpace` and `locusFunctor` give the actual
affinoid, spectrum and subspace realizations. `boundedPresheaf` and
`banachPresheaf` retain all original quotient algebras, norms and bounded maps.
`sameChartFunctor` retains every original full-domain representation and
restriction. It is fully faithful: the structural equation at that same
original chart recovers exactly the original base equation, constructing
the inverse on arrows. The displayed restriction and affinoid realization
formulas are definitional.

`isoOfLocusEq` constructs an isomorphism between any two presentations with
the same ambient locus, including across unrelated original charts. The inverse
equations follow from proved uniqueness of actual arrows. Conversely any
isomorphism implies equality of ambient loci.
`boundedEquivOfIso` and `boundedEquivOfLocusEq` retain the mutually inverse
actual bounded maps on the original quotient algebras.
`spectrumHomeomorphOfLocusEq` is their actual spectrum homeomorphism and commutes
with the ambient maps.

This is an internal derived construction from unrestricted bounded local-domain
restrictions, their full representation and coherence, original full-domain
uniqueness, and actual domain spectrum embeddings. The earlier directed-domain
category is a related special case; this construction removes its directedness
requirement using the newly constructed unrestricted maps. No new original-source
assertion, assumed analytic output or peer draft is used. Arbitrary positive
radii, trivial valuations, nonreduced or zero quotients and permitted empty
covers remain included. The entire extended atlas and its net, analytic or
equivariant sites and the Harris tower remain further work.
