# Conjugation of finite invariant rational sites

This derived local construction transports the published invariant rational
categories and their finite covering topologies by actual bounded algebra
automorphisms. It constructs an equivalence with continuous forward and inverse
functors and gives precomposition on categorical sheaves.

Let `K` be a complete ultrametric normed field, `P` an actual presented strict
affinoid algebra over `K`, `G` a topological group, and
`ρ : RationalSpectralAction G P`. The field and group have independent universes.
This action is continuous for the published restricted rational spectral
topology. Objects retain chosen unit-radius rational presentations; arrows
retain locus inclusions and their actual bounded quotient restriction maps.

## Conjugating the subgroup and the domains

`conjugateOpenSubgroup U g` is the inverse image of the open subgroup `U` under
the continuous homomorphism given by conjugation by `g⁻¹`. Its membership
criterion is

`k ∈ conjugateOpenSubgroup U g ↔ g⁻¹ * k * g ∈ U`.

Thus this is the actual open subgroup `gUg⁻¹`.
`conjugateOpenSubgroup_inv` proves that conjugating this subgroup by `g⁻¹`
recovers `U` exactly, using the group identities.

`mem_locusOpenSubgroup_smul_iff` pulls the published
`conj_mem_locusStabilizer_iff` back along the actual homomorphism `ρ.toMonoidHom`.
It identifies preservation of the moved rational locus by `k` with preservation
of the original locus by `g⁻¹ * k * g`. The resulting equality
`locusOpenSubgroup_smul` identifies the moved open stabilizer with its conjugate.

For any open `V ≤ conjugateOpenSubgroup U g`,
`invariantTransportFunctor g h` sends a `U`-invariant object `d` to the actual
rational presentation `ρ.toMonoidHom g • d.obj`, proved `V`-invariant by this
criterion. It maps each inclusion using the existing `actionFunctor`.
`invariantTransportFunctor_forget` identifies the forgotten functor exactly with
the original inclusion followed by that rational action functor.
`invariantTransport_restriction` records the commuting formula for the actual
bounded quotient comparison and restriction maps. It is the published
`restriction_transport` specialized to these invariant objects and arrows.

`invariantConjugationEquivalence U g` uses the target subgroup `gUg⁻¹` itself.
Its inverse transports by `g⁻¹`, with the subgroup containment supplied by
`conjugateOpenSubgroup_inv`. The unit and counit come from the inverse action
identities on the chosen rational data. Each is lifted to the full invariant
subcategory. Thinness of the locus-inclusion categories proves naturality and
the equivalence coherence equation.

## Finite covers

`invariantTransport_isFiniteCovering_pushforward` moves the finite covering
family witnessing membership of a sieve in the published finite rational
topology. Each image arrow belongs to the pushforward sieve, and the published
`familyCovers_smul_iff` proves that its actual moved loci cover the moved target.

Conversely, `invariantTransport_isFiniteCovering_of_pushforward` extracts a
finite covering family from the image sieve and chooses an original sieve arrow
through which each image-family arrow factors. For an original target point
`x`, its image `ρ.toMonoidHom g • x` lies in one of the covering domains. The
factorization puts this image in the moved original domain. The published
`smul_mem_smul_locus_iff` then puts `x` in the original domain. Hence the finitely
many chosen original sieve arrows cover.

`invariantTransport_pushforward_mem_iff` packages this preservation and reflection
for every sieve, and `invariantTransport_coverPreserving` supplies Mathlib's
`CoverPreserving` interface. These results also allow the smaller target subgroup
`V` above. Cover index types have the field universe, as in the existing finite
invariant topology. Empty covering families and empty loci are retained.

## Continuity and sheaves

For the canonical equivalence, every comparison object is isomorphic to the
image of its inverse transport. The counit gives that isomorphism for the
forward functor; the inverse unit gives it for the inverse functor. Fullness
and faithfulness of the equivalence and Mathlib's
`compatiblePreservingOfDownwardsClosed` therefore prove compatibility preservation
in each direction, including comparisons through objects outside a chosen
literal image. The compatibility lemmas allow any coefficient universe.

`invariantConjugation_isContinuous` and
`invariantConjugationInverse_isContinuous` combine this compatibility with the
cover-preserving results via `Functor.isContinuous_of_coverPreserving`.
`invariantSheafConjugation U g A` is the resulting precomposition functor from
sheaves on the `gUg⁻¹`-invariant finite rational site to sheaves on the
`U`-invariant site, for an arbitrary coefficient category `A`. Its underlying
presheaf is exactly precomposition by the opposite of the forward domain
functor, as `invariantSheafConjugation_obj` states. Coefficient objects and homs
have independent universes. This uses already given sheaves; a sheaf property
for the actual quotient-algebra presheaf remains a separate obligation.

## Provenance and scope

Berkovich's unfinished 1995-1996 manuscript *Etale equivariant sheaves on p-adic
analytic spaces*, section 1.1, printed/PDF p.3, describes the group action on
spaces with open-subgroup actions by changing the group through conjugation.
Section 1.2 on the same page defines equivariant etale and quasi-etale covering
families using the underlying geometric covers. Registered source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf*, digest
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The source's conjugation convention agrees with `gUg⁻¹` here.

Those passages motivate this restricted construction. The implemented finite
rational-site equivalence is derived from the published `RationalAutomorphism`,
`SpectralTransport`, `SpectralContinuousAction` and `InvariantRationalSite`
interfaces. It is not a verbatim assertion of the manuscript. The categorical
continuity and sheaf construction use Mathlib's
`CategoryTheory/Sites/CoverPreserving.lean` and
`CategoryTheory/Sites/Continuous.lean`.

The scope is the fixed-field, unit-radius rational sites for the given
restricted rational spectral action. General analytic atlases, arbitrary-radius
analytic domains, etale and quasi-etale morphisms and sites, induced analytic
spaces, structure sheaves, Tate acyclicity and cohomology remain separate.
