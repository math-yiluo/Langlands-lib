# Functoriality of finite spectral-invariant rational sites

Authors: Worker 56 and Worker 36. Internal adaptation of their published
`RationalNormInvariantRestrictionSite` construction to the represented-domain
spectral action and its full invariant rational category.

The inputs are a complete ultrametric normed field `K`, an actual
`PresentedAffinoidAlgebra K`, a topological group `G`, and a
`DomainSpectralAction G A`. This action supplies continuity for its tests on
represented affinoid domains. No continuity in the quotient-algebra norm of
each base-algebra orbit is assumed. The existing category
`SpectralInvariantChart ρ H` is the full category of actual positive-radius
rational charts with `H ≤ ρ.locusOpenSubgroup d.toDomain`. It retains every
original bounded restriction over `A`. Field and group universes are
independent.

The module constructs functoriality for two full inclusions. For open
subgroups `V ≤ U`, the existing `spectralInvariantChartRestriction` sends a
`U`-invariant chart to the same chart with its proved `V`-invariance.
The abbreviation `spectralInvariantChartInclusion` is the original full
inclusion of `H`-invariant charts into all `RationalChart K A` objects.
Both retain the actual quotient algebras, bounded maps, loci and point
topologies.

`spectralInvariantRestriction_whole` and
`spectralInvariantRestriction_inter` identify the subgroup-restricted whole
and intersection charts exactly with their constructed versions for `V`.
The intersection uses the product positive polyradius and the original
quotient presentation. `spectralInvariantRestrictionInterLift` accepts
two restrictions from any `V`-invariant chart to the images of two
`U`-invariant charts and constructs the restriction to their unchanged
intersection. Its source need not be `U`-invariant. It wraps the actual
bounded quotient intersection lift.
`spectralInvariantRestrictionMapConeIsLimit` uses this lift and the proved
uniqueness of bounded restrictions to establish the image pullback cone's
universal property. Two preservation instances show that subgroup change
preserves terminal objects and each pullback of restrictions.

For the ordinary inclusion, `spectralInvariantInclusionInterLift`
accepts any actual rational source with restrictions to the two invariant
charts and uses the same bounded quotient lift. It imposes no invariance
condition on its source. `spectralInvariantInclusionMapConeIsLimit` proves
the image cone's universal property. The two preservation instances retain
the whole quotient as a terminal object and preserve pullbacks of
restrictions.

For each inclusion, the theorem with suffix
`_isFiniteCovering_pushforward` uses the images of the original finite
covering family. The unchanged loci still cover the target. The converse
`_isFiniteCovering_of_pushforward` starts from a finite cover in the image
sieve. Each covering arrow factors through the image of an original
sieve arrow. Choosing one factorization for each covering arrow gives
finitely many arrows in the original sieve. Their loci contain the
covering loci by the actual restriction's subset property, so they cover
the original target. The target category can contain objects outside the
inclusion's image.

The two `_pushforward_mem_iff` theorems preserve and reflect covering of
every original sieve. The two `_coverPreserving` theorems package
preservation as Mathlib's `CoverPreserving`. The two `_ofArrows_mem_iff`
theorems compare the generated covering sieves of any finite family and
its image through their identical point-coverage criteria. Covering
witnesses use index types in the field universe, as in the underlying
finite rational topologies. Empty indexing types are allowed.

The two `_compatiblePreserving` proofs compare a compatible family first
on the actual invariant intersection. Applying the contravariant
presheaf map along the constructed intersection lift gives equality on
every comparison chart of the target category. The subgroup-change proof
therefore includes sources invariant only under `V`, and the ordinary
inclusion proof includes sources without any `H`-invariance.
All comparisons use the original bounded restrictions. Together with
cover preservation, Mathlib's
`Functor.isContinuous_of_coverPreserving` yields the two `_isContinuous`
instances for these finite sites.

`spectralInvariantSheafRestriction` sends sheaves on the `V`-invariant
finite site to sheaves on the `U`-invariant finite site, for any coefficient
category `E`. `spectralInvariantSheafInclusion` sends ordinary finite
rational sheaves to sheaves on the `H`-invariant finite site. Both use
`sheafPushforwardContinuous`. Their `_obj` theorems identify the
underlying presheaf exactly with precomposition by the opposite
inclusion functor. Coefficient objects and homs have independent
universes, also independent of the field and group universes.
These functors act on already given sheaves; no sheaf property of the
quotient-algebra presheaf is assumed or proved.

All spectral-action declarations retain completeness of `K`, as required
by the represented-domain spectral action input. The private ordinary
chart-uniqueness lemma uses only the underlying bounded restriction
category and omits this unused assumption.

The geometric conventions are Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), printed/PDF p.9, Definition 2.2.1 and
Exercise 2.2.2(ii)-(iii), and p.10, Fact 2.2.3(i) and Definition 2.2.7.
Registered source: `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These passages fix represented domains, positive-radius rational
quotients, intersections, spectrum-locus identification and bounded
domain embeddings. The inherited rational data retain explicit unit
generation, a sufficient condition for absence of common zeros; no
converse is claimed.

Berkovich's unfinished 1995-1996 manuscript, *Etale equivariant sheaves
on p-adic analytic spaces*, section 1.1, printed/PDF pp.1-3, defines
continuous analytic actions, equivariant morphisms and morphisms with a
continuous homomorphism between acting groups. Section 1.2, p.3, defines
equivariant etale and quasi-etale covers through the underlying geometric
families and describes the resulting site/sheaf functoriality.
Registered folder:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF member *Berkovich--Etale equivariant sheaves on p-adic analytic
spaces (unfinished manuscript)--1996.pdf*, SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

These sources motivate the conventions; they do not state this finite
rational-site construction. The arguments adapt the published
`RationalNormInvariantRestrictionSite` proofs, replacing their action,
invariant site and subgroup-change inputs by the spectral versions.
Mathlib's `CategoryTheory/Sites/CoverPreserving.lean` and `Continuous.lean`
supply the general continuity and categorical sheaf packaging.
The construction does not compare the represented-domain spectral
topology with the manuscript's full topology, which also uses compact
analytic-domain tests, or with quotient-norm orbit continuity.

Arbitrary positive real radii, trivial valuations, nilpotents, zero
quotients, empty loci and covers of empty targets remain allowed.
This is a local finite rational-site construction. Analytic-algebra
sheafness, general analytic atlases, analytic etale and quasi-etale
morphisms and sites, compact and distinguished-domain lifting and
the Harris tower remain separate obligations.
