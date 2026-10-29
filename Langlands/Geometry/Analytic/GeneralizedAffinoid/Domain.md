# Domain representations tested on all presented affinoids

Author: Worker 56.

This module defines affinoid-domain representations over the actual finite
positive-polyradius quotient algebras and constructs their restriction
category. The universal property tests every such presented affinoid algebra,
including presentations with arbitrary positive real radii. The identity
algebra map supplies a constructed example representing the whole spectrum.

## Algebras, hypotheses and morphisms

The coefficient field `K : Type u` has `NormedField K` and
`IsUltrametricDist K`. The imported `PresentedAffinoidAlgebra K` stores a
finite positive polyradius and a closed ideal in the corresponding weighted
Tate algebra. Its carrier is the actual ring quotient, equipped with its
quotient norm and `K`-algebra structure. When `CompleteSpace K` is available,
the imported `Banach` module proves completeness of these quotient norms.
No nontriviality hypothesis is imposed on the quotient algebra, and trivial
valuations on `K` are allowed.

All algebra maps below are `BoundedAlgHom K`, so they are unital
`K`-algebra homomorphisms satisfying an actual norm bound. Their induced
spectrum maps are the existing `BanachSpectrum.comap`, which pulls back
bounded multiplicative seminorms. `HasImageIn K φ U` says that each point
of the target algebra's spectrum pulls back to a point in `U`. This
predicate is defined without a completeness hypothesis.

## The representation predicate and its example

For `i : BoundedAlgHom K A B` and a subset `U` of `BanachSpectrum A`,
`Represents K i U` is the following proposition, over complete `K`:

1. `U` is closed.
2. The range of the actual spectrum map induced by `i` equals `U`.
3. For every `R : PresentedAffinoidAlgebra K` and every bounded
   `φ : A → R` with `HasImageIn K φ U`, there is exactly one bounded
   `ψ : B → R` with `ψ.comp i = φ`.

The equation in the last clause is the algebra equation corresponding to
factorization of the contravariant spectrum morphism. There is no strictness
restriction on `R`. The test category consists of the chosen presentations
already constructed in the Library; this module does not establish an
equivalence with a separate category of abstract affinoid Banach algebras.

`Represents.hasImageIn` derives image containment from the range equality.
`represents_id` proves the entire predicate for the bounded identity of `A`
and the whole spectrum: closedness is immediate, comap of the identity fixes
each seminorm, and the unique factorization of `φ` is `φ` itself.

`Domain K A` stores a presented algebra, an actual bounded map from the
fixed base `A`, a subset of its spectrum, and the representation proof.
The module defines a representation by its mathematical universal property;
it does not supply a general existence theorem for prescribed subsets.
`Domain.whole K A` is the example constructed from `represents_id`.

## Actual restrictions and their category

For domains `U` and `V` over `A`, `Domain.Inclusion U V` stores a
bounded algebra restriction
`V.algebra → U.algebra` whose composite with `V.baseMap` is
`U.baseMap`. Thus arrows have the direction of domain inclusions and the
opposite direction from algebra maps.

`Inclusion.subset` proves that each such restriction entails
`U.locus ⊆ V.locus`. For a point in `U.locus`, the exact range condition
provides a spectrum point of `U.algebra`. Pulling that point back along the
restriction gives a point of `V.algebra`; the equation over `A` identifies
its base image with the original point.

The universal property of `V`, tested on the actual algebra `U.algebra`,
proves that any two restrictions agree. This gives
`Subsingleton (Inclusion U V)`. Identity arrows and composition are
constructed from bounded identity maps and composition of the stored
restrictions. Their equations over `A` follow from the corresponding
equations of the factors. The resulting `Category (Domain K A)` uses the
proved uniqueness to establish its laws.

`inclusionOfSubset U V h` constructs a bounded restriction from an actual
subset inclusion `h`. The range condition for `U` makes `U.baseMap` an
eligible test map into `V.locus`; the full universal property of `V`
then provides its unique factorization. In particular,
`nonempty_hom_iff_subset` proves
`Nonempty (U ⟶ V) ↔ U.locus ⊆ V.locus`. Existence of a bounded
restriction is obtained from the representation proof, rather than
defined to be mere subset containment.

`wholeIsTerminal` constructs the categorical terminal witness for the
whole-spectrum domain. Its arrows are `inclusionOfSubset` applied to
containment in the whole spectrum, and uniqueness is the subsingleton
result above. The terminal domain's algebra is exactly `A`.

## Spectrum and subspace realizations

`Domain.spectrumMap U` is the continuous structural spectrum map.
`spectrumToLocus U` corestricts it to `U.locus`, using the proved image
containment. `spectrumToLocus_surjective` follows from the exact range
clause of `Represents`.

For an inclusion `f : U ⟶ V`, `Inclusion.spectrumMap f` pulls back
seminorms along its stored bounded restriction.
`spectrumMap_over_base` proves the resulting triangle over the base
spectrum commutes by evaluating the algebra equation on each element
of `A`. `locusMap f` is the continuous subtype inclusion.
`spectrumToLocus_naturality` identifies these two routes to `V.locus`.

`toAffinoidSpace` sends each domain to the opposite of its actual algebra
and each inclusion to the opposite of its stored restriction.
`toTopologicalSpace` composes this functor with the existing actual
affinoid spectrum functor. `locusFunctor` sends each domain to its
represented subset with the subspace topology and each arrow to its
continuous inclusion. `spectrumToLocusNat` packages the preceding
commutativity proof as a natural transformation from the spectrum
realization to the locus realization.

Only continuity and surjectivity of `spectrumToLocus` are proved here.
Injectivity, a homeomorphism onto the locus, existence of other domains,
and closure under domain intersections remain separate construction
obligations. This module also supplies no structure sheaf, general
analytic-space atlas, etale site or equivariant site.

## Source correspondence and derived content

The original source is V. G. Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, with PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Definition 2.1.11, printed/PDF p. 8, defines affinoid spaces as the
category dual to affinoid algebras with bounded homomorphisms.
Definition 2.2.1, p. 9, defines an affinoid domain by closedness, the
exact image of its structural morphism, and unique factorization for
every affinoid test morphism whose image lies in the domain.
`Represents` translates these clauses into the existing category of
finite positive-polyradius quotient presentations. The completeness
hypothesis follows the complete-field setting of the source.
Definition 2.2.7, p. 10, gives the affinoid-domain-embedding category
which motivates the fixed-base restriction category here.

The stored presentation data, algebra equation for restrictions,
constructed category, containment criterion, terminal object and
realization functors are internal consequences and categorical
packaging of this predicate and the Library's actual bounded-map and
spectrum constructions. The identity example proves this predicate
for a specific map. The source's stronger spectrum identification in
Fact 2.2.3(i), p. 10, is not asserted as proved by this module.
