# Finite coverings of invariant rational quotient domains

Author: Worker 36.

This is an internal derived construction on the existing
`InvariantRationalDomain ρ U`. The scalar field `K` is a complete
ultrametric normed field in universe `u`, `P` is an actual presented strict
affinoid algebra over `K`, and `ρ : RationalSpectralAction G P` is the
published action of a topological group in independent universe `v`.
The subgroup `U` is open. Objects retain their actual rational input,
closed-ideal Tate quotient, bounded structural map and quotient spectrum.
Morphisms are inclusions of the actual rational loci, with the previously
constructed contravariant bounded restrictions and continuous equivariant
spectrum maps. No analytic structure or descent output is assumed.

The theorem `mem_locusOpenSubgroup_inter` proves that an ambient operator
stabilizing each of two loci stabilizes their constructed rational
intersection. The proof uses the existing equality between the constructed
intersection locus and the set intersection, and the fact that image under
an injective spectrum operator preserves intersection.

In the namespace `InvariantRationalDomain`, `whole ρ U` equips the existing
empty-numerator rational presentation with its proved invariance.
`toWhole` retains the existing inclusion, and `wholeIsTerminal` proves the
terminal universal property using uniqueness of inclusion morphisms.
`inter ρ U d e` retains the published product-denominator intersection
presentation and its genuine quotient algebra; its invariance is proved
using the preceding stabilizer theorem. `inter_obj` and `locus_inter`
record the underlying presentation and actual locus. `interLeft`,
`interRight` and `interLift` lift the existing inclusions unchanged.
`pullbackCone` and `pullbackConeIsLimit` prove the pullback universal
property in this category of invariant rational inclusions. This is a
pullback assertion in the specified inclusion category.

`IsFiniteCovering ρ U S` means that the sieve `S` contains a finite
family of invariant rational inclusions whose loci cover its target
locus. Its index type belongs to universe `u` and may be empty. The
predicate uses the published `RationalData.FamilyCovers`, evaluated on the
actual underlying rational data. The proofs parallel the published finite
rational topology, with invariance now proved for every constructed
intersection:

- The identity singleton gives `isFiniteCovering_top`.
- `IsFiniteCovering.pullback` intersects each covering domain with the
  source. Each new domain is invariant. The two arrows to the old target
  agree by thinness, so downward closure places the new inclusion in the
  pulled-back sieve. The locus-intersection equality proves it covers.
- `IsFiniteCovering.transitive` composes the inclusions and uses a
  dependent sum of finite index types. Successive applications of the
  point-covering hypotheses give the composite point cover.

These proofs construct `finiteRationalTopology ρ U`, a genuine
Grothendieck topology on the actual invariant rational inclusion category.
`mem_finiteRationalTopology` unfolds its sieve criterion.
`ofArrows_mem_finiteRationalTopology_iff` proves that the sieve generated
by a finite invariant family covers precisely when the family's loci
cover: membership of a witness arrow in the generated sieve supplies a
factorization through one of the generating domains.
`bot_mem_finiteRationalTopology_iff` proves that the empty sieve covers
exactly those objects whose actual locus is empty. Its reverse direction
uses the empty index type, without requiring a point or a nonzero quotient.

`familyCovers_iff_jointly_surjective` identifies locus covering with joint
surjectivity of the genuine continuous equivariant maps in
`invariantSpectrumFunctor ρ U`. This equivalence holds even without
finiteness of the index type. In the forward direction, a quotient spectrum
point maps into the target locus. A covering locus supplies a preimage in
one covering quotient using the published range equality. The structural
triangle for bounded restriction and injectivity of the target's
structural spectrum map show that its image is the original quotient
point. Conversely, lift a target locus point to its quotient spectrum,
use joint surjectivity, and apply that same structural triangle. Thus the
covering condition is a condition on the actual spectra and their
equivariant maps, as well as on their represented loci.

The original geometric context is Berkovich's *Non-archimedean analytic
spaces*, Trieste lectures (2009), Definition 2.2.1 and
Exercise 2.2.2(ii)–(iii), printed/PDF p.9: representing affinoid domains,
rational quotient construction and stability under intersections. The
existing Library's restricted unit-radius constructions supply the
representations and maps used here. The invariant-category topology is
derived from those constructions and elementary finite-cover arguments.
It does not assert Tate acyclicity from Fact 2.2.6(i), p.10.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces* (1995–1996), section 1.1, printed/PDF pp.1–2, motivates the
continuous action and equivariant morphisms. Section 1.2, printed/PDF p.3,
defines equivariant etale and quasi-etale sites by equivariant objects and
underlying geometric covering families. The present finite rational
topology is a restricted local prerequisite with that underlying-cover
pattern. It does not define those full sites, establish that all their
objects are rational domains, or identify this topology with either of
them. It also does not identify the restricted rational spectral
automorphism topology with the manuscript's full analytic topology.

Trivial valuations, zero or nonreduced quotient algebras, and empty spectra
remain allowed. Sheafness of quotient sections, finite scalar gluing,
analytic atlases, arbitrary-radius domains, etale/quasi-etale morphisms
and Harris towers remain separate obligations.

The Trieste source is registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The manuscript source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its PDF member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
