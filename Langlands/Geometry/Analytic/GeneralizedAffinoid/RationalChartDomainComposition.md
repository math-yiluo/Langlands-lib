# Full domains inside actual rational charts

Author: Worker 56.

This module constructs a full represented domain over the original base from
a full represented domain over an actual rational quotient. The coefficient
field is complete and ultrametric; all algebras are the Library's finite
positive-polyradius Tate quotients, including zero algebras and nilpotents.

## Representation and its composition

`Represents.comp_of_injective` takes full representation proofs for bounded
maps `i : A → B` and `j : B → C`, and injectivity of the actual spectrum
map induced by `i`. It proves full representation for `j.comp i` on the
image under that spectrum map of the inner domain locus.

Closedness follows from compactness of the closed inner locus and continuity
into the Hausdorff base spectrum. The exact spectrum image follows by composing
the two actual spectrum maps. A test map into the composite locus first
factors uniquely through `B`. Injectivity of the outer spectrum map shows
that this factor has image in the inner locus, so it factors uniquely through
`C`. Composing the two base equations gives existence for the composite;
the two uniqueness properties give uniqueness.

## The actual rational construction

For `d : RationalChart K A`, `spectrumMap_injective` follows from the published
homeomorphism `d.locusHomeomorph`. Thus `extendDomain d U` needs only an
actual full domain `U : Domain K d.algebra`; it requires no additional
injectivity or factorization witness.

The constructed domain has exactly `U.algebra`, bounded structural map
`U.baseMap.comp d.baseMap`, and locus `d.spectrumMap '' U.locus`.
Its full representation proof is the preceding composition theorem applied
to the two already proved representation properties. The projection lemmas
are definitional. Its locus lies in `d.locus`.

`extendDomainInclusion d U` is an actual inclusion into `d.toDomain`.
Its stored bounded restriction is precisely `U.baseMap`.
`extendDomainFunctor d` retains every inner bounded restriction and composes
its base equation with the rational base map. `fullyFaithfulExtendDomain d`
constructs the inverse on homs by retaining that same bounded map. The
published uniqueness of bounded maps out of the rational quotient recovers
the equation over `d.algebra` from the equation over `A`. Extensionality
proves both inverse equations, giving the `Full` and `Faithful` instances.
The actual affinoid and spectrum realization functors are unchanged
definitionally.

## Original source and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1, printed/PDF p.9, gives the full domain representation
property; Exercise 2.2.2(ii) gives positive-radius rational quotients.
Fact 2.2.3(i), p.10, gives the spectrum identification context, and
Definition 2.2.7 gives the domain-embedding category. These original
pages were read directly.

The composition theorem, actual domain construction and fully faithful
functor are internal consequences of these published Library constructions,
with proofs described above. The generic theorem explicitly retains its
injectivity hypothesis; the actual rational construction supplies it by
proof. This module does not flatten an iterated rational presentation into
rational data over `A`, so it does not prove the stronger rational-type
assertion of Exercise 2.2.4. It provides no arbitrary affinoid tensor
product, general domain base change, structure-sheaf descent, general
analytic atlas or etale/equivariant site.
