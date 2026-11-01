# Functoriality of finite norm-invariant weighted rational sites

Authors: Worker 56 and Worker 36. Internal adaptation of the published strict
`InvariantRestrictionSite` construction to actual positive-radius rational
quotients and norm-continuous base-algebra actions.

The inputs are a complete ultrametric normed field `K`, an actual
`PresentedAffinoidAlgebra K`, a topological group `G`, a homomorphism
`ρ : G →* Aut A` of bounded algebra automorphisms, and continuity in norm of
each forward base-algebra orbit. The existing category
`NormInvariantChart ρ hρ H` is the full category of actual weighted rational
charts whose loci are preserved by the open subgroup `H`. Every original
bounded restriction over `A` is retained. Field and group universes are
independent.

The module constructs functoriality for two existing full inclusions. For
open subgroups `V ≤ U`, `normInvariantChartRestriction` sends a `U`-invariant
chart to the same chart with its proved `V`-invariance. The abbreviation
`normInvariantChartInclusion` is precisely the original full inclusion of
`H`-invariant charts into all `RationalChart K A` objects. Neither operation
changes a quotient algebra, bounded map, locus or underlying point topology.

`normInvariantRestriction_whole` and `normInvariantRestriction_inter`
identify the subgroup-restricted whole and intersection charts exactly with
their already constructed versions for `V`. The actual intersection uses the
product positive polyradius and the original quotient presentation.
`normInvariantRestrictionInterLift` accepts two restrictions from any
`V`-invariant chart to the images of two `U`-invariant charts and constructs
the restriction to their unchanged intersection. Its source need not be
`U`-invariant. The construction wraps the published bounded quotient
intersection lift. `normInvariantRestrictionMapConeIsLimit` uses it and
proved uniqueness of actual restrictions to establish the image pullback
cone's universal property. The two preservation instances show that
subgroup change preserves terminal objects and each pullback of restrictions.

The analogous ordinary inclusion construction is
`normInvariantInclusionInterLift`. It accepts any actual rational source,
with no invariance hypothesis, and uses exactly the same bounded quotient
lift. `normInvariantInclusionMapConeIsLimit` proves the ordinary image
cone's universal property. Its two preservation instances retain the whole
quotient as a terminal object and preserve pullbacks of restrictions.

For each functor, the theorem with suffix
`_isFiniteCovering_pushforward` uses the images of the original finite
covering family. Its loci are unchanged, so the same family covers the
target. The converse `_isFiniteCovering_of_pushforward` begins with a finite
cover in the image sieve. Each covering arrow factors through the image of
an original sieve arrow. Choosing such a factorization for each member
produces finitely many original arrows in the original sieve. Their loci
contain the covering loci by the actual restriction's subset property,
so they cover the original target. This does not require all charts of the
target category to lie in the functor's image.

The two `_pushforward_mem_iff` theorems therefore preserve and reflect
covering of every original sieve; the two `_coverPreserving` theorems
package preservation as Mathlib's `CoverPreserving`. The two
`_ofArrows_mem_iff` theorems compare the generated covering sieves of any
finite family and its image directly, by their identical point-coverage
criteria. All covering witnesses use index types in the field universe,
as in the underlying finite rational topologies; empty index types are
allowed.

The two `_compatiblePreserving` proofs compare a compatible family first
on the actual invariant intersection. Pulling this equality back along
the constructed intersection lift gives equality on every comparison
chart of the target category. Thus the subgroup-change proof includes
sources invariant only under `V`, and the ordinary-inclusion proof includes
sources without any `H`-invariance. The full compatibility condition is
proved using the original bounded restrictions and their contravariant
presheaf maps. Together with cover preservation, Mathlib's
`Functor.isContinuous_of_coverPreserving` yields the two `_isContinuous`
instances for these actual finite sites.

`normInvariantSheafRestriction` sends sheaves on the `V`-invariant finite
site to sheaves on the `U`-invariant finite site, for any coefficient
category `E`. `normInvariantSheafInclusion` sends ordinary finite rational
sheaves to sheaves on the `H`-invariant finite site. Both use
`sheafPushforwardContinuous`. Their `_obj` theorems state that the underlying
presheaf is exactly precomposition with the opposite inclusion functor.
Coefficient objects and homs have independent universes, also independent
of the field and group universes. These functors act on already given
sheaves. They assume no sheaf property of the quotient-algebra presheaf.

The whole/intersection object identities and the four covering-predicate
preservation/reflection proofs do not require completeness of `K`.
The actual bounded intersection lift, limit assembly, finite Grothendieck
topologies, continuity and sheaf functors use the complete-field setting.

The underlying geometric conventions are Berkovich, *Non-archimedean
analytic spaces* (Trieste lectures, 2009), printed/PDF p.9, Definition
2.2.1 and Exercise 2.2.2(ii)-(iii), and p.10, Fact 2.2.3(i) and Definition
2.2.7. Registered source: `berkovich-2009-trieste-analytic-spaces`, PDF
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Those passages fix represented domains, weighted rational quotients,
intersections, spectrum-locus identification and bounded domain embeddings.
The inherited rational data retain explicit unit generation, a sufficient
condition for absence of common zeros; no converse is claimed.

Berkovich's unfinished 1995-1996 manuscript, *Etale equivariant sheaves
on p-adic analytic spaces*, section 1.1, printed/PDF pp.2-3, defines
continuous actions, equivariant morphisms and morphisms with a continuous
homomorphism between acting groups. Section 1.2, p.3, defines equivariant
etale and quasi-etale covers using the underlying geometric families and
describes the resulting site/sheaf functoriality. Registered folder:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf*, SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

These sources motivate the conventions; they do not state this finite
rational-site construction. The new arguments adapt the published strict
`InvariantRestrictionSite` proofs, replacing their geometric inputs by
the actual weighted chart, norm-invariant site and subgroup-restriction
constructions. Mathlib's `CategoryTheory/Sites/CoverPreserving.lean` and
`Continuous.lean` supply the general continuity and sheaf packaging.
The full analytic automorphism topology is not identified with the
explicit norm-orbit hypothesis.

Arbitrary positive real radii, trivial valuations, nilpotents, zero
quotients, empty loci and covers of empty targets remain allowed.
This is a local finite rational-site construction. Analytic-algebra
sheafness, general analytic atlases, analytic etale and quasi-etale
morphisms and sites, compact and distinguished-domain lifting and the
Harris tower remain separate obligations.
