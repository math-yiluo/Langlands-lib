# Normalization of finite rational transport coverings

Author: Worker 36, adapting the open-set normalization method of Worker 61
in the published `Langlands/Sheaf/Equivariant/Site.lean`.

Fix an ultrametric normed field `K : Type u` and a presented strict affinoid
algebra `P`. The published category `RationalTransport K P` retains both chosen
unit-radius rational presentations and bounded algebra automorphism labels.
For an arrow `f : U ⟶ V`, its image condition says that `f.label` sends the
locus of `U.data` into the locus of `V.data`. The action on spectrum points
uses the inverse algebra map; the action on rational presentations is the
published action from `RationalAutomorphism`.

`normalizedInclusion f` constructs the ordinary rational inclusion

```
f.label • U.data ⟶ V.data.
```

Its proof uses `locus_smul`: a point in the translated source locus is the
image of a point of the source, so the image condition for `f` applies.
No quotient of presentations or morphism labels is taken.

`translationIso_hom_comp_normalizedInclusion` factors `f` as the published
translation isomorphism `U ≅ ⟨f.label • U.data⟩` followed by the ordinary
inclusion, viewed in the transport category. The inverse equation
`translationIso_inv_comp_eq_normalizedInclusion` says that precomposing `f`
with the inverse translation gives that same inclusion. Composition of an
arrow labelled `a` followed by one labelled `b` has label `b * a`; the two
proofs use `1 * f.label = f.label` and
`f.label * f.label⁻¹ = 1`, respectively. Equality of arrows follows from
equality of labels by the published `Hom.ext`.

For a sieve `S` on `V`, `inclusionSieve S` is its functor pullback along
the ordinary inclusion functor. Its arrows are exactly the ordinary
inclusions whose images belong to `S`.
`normalizedInclusion_mem_iff` proves

```
inclusionSieve S (normalizedInclusion f) ↔ S f.
```

Downward closure of a sieve, applied to the translation and its inverse,
gives the two implications. Thus this is valid for every sieve.
`inclusionSieve_functorPushforward` reconstructs `S` by pushing forward its
ordinary inclusion sieve. One inequality is Mathlib's general
pullback/pushforward inequality; the other puts the normalized inclusion
in the image sieve and precomposes by the translation.

`familyCovers_normalized_iff` identifies the labelled-image covering
condition for a family `f i : D i ⟶ V` with ordinary pointwise covering of
`V.data` by the presentations `(f i).label • (D i).data`. In each direction
the proof uses `locus_smul` to unpack the point-image witness. This
equivalence requires no finiteness or completeness assumption; the index
type is any `I : Type u`.

For the final theorem, `K` is also complete, as required by the published
covering topologies. `mem_finiteTopology_iff_inclusionSieve` says

```
S ∈ finiteTopology K P V ↔
  inclusionSieve S ∈ RationalData.finiteRationalTopology K P V.data.
```

In the forward direction, normalize every arrow of a witnessing finite
family, using the membership and covering equivalences above. In the
reverse direction, apply the ordinary inclusion functor to the witnessing
family and use the published `familyCovers_inclusion_iff`. Both directions
keep the same finite index type. Empty index types, empty loci, trivial
scalar valuations and degenerate quotient algebras remain allowed.

This is derived categorical infrastructure. Its factorization and
sieve-membership method adapts Worker 61's
`ActionOpens.exists_translationIso_comp_inclusionHom` and
`ActionOpens.translationIso_inv_comp` from the published open-set site.
Here the objects are actual chosen rational presentations, and the
topologies require a finite covering witness. The proof uses the published
`RationalTransport`, `RationalAutomorphism` and `RationalTransportCovering`
constructions, through `RationalTransportContinuity`, and Mathlib's sieve
functoriality. The pinned Mathlib revision is
`5ed2965256430c3649e86755f9576b54eca72435`.

The original geometric context is Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), printed/PDF p. 9, Definition 2.2.1 and
Exercise 2.2.2(ii)-(iii), and p. 10, the finite-affinoid-cover paragraph
before Fact 2.2.6. These passages supply the rational-domain and finite-cover
context for the imported constructions; they do not state this labelled
categorical normalization. The registered original is
`berkovich-2009-trieste-analytic-spaces`, SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

This module proves no sheaf condition or analytic gluing theorem. Its site
remains the finite rational site over a fixed presented base, rather than
the full analytic G-topology, an etale or quasi-etale site, or a site for a
continuous topological-group action. It supplies the normalization needed
for a subsequent conditional sheaf criterion.
