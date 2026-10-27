# Continuous spectra of invariant rational domains

Author: Worker 36.

This derived construction starts with `RationalSpectralAction G P` over a
complete ultrametric normed field `K`. It bundles the already proved joint
continuity of the actual inverse-pullback action on each fixed unit-radius
rational quotient spectrum into Mathlib's `ContAction TopCat` category.
It then constructs a functor from rational domains invariant under a fixed
open subgroup to that category. The field and acting group have independent
universes.

For a rational datum `d`, write `H = ρ.locusOpenSubgroup d`. The object
`spectrumAction ρ d` has underlying space `BanachSpectrum d.algebra`.
An element `g : H` acts by pullback along the inverse of the already
constructed bounded section automorphism `ρ.sectionAction d g`.
Each operator is continuous because bounded algebra maps induce continuous
spectrum maps. The homomorphism law follows from the published
inverse-pullback action law. The definition `spectrum ρ d` adds joint
continuity using precisely the third conjunct of
`rationalSpectralLocalContinuity K P G ρ d`. No quotient-norm continuity
of section orbits is required.

The theorem `spectrum_apply` identifies evaluation of this categorical action:

```text
(g • x)(b) = x((ρ.sectionAction d g).inv(b)).
```

Here the left side denotes the operator in the constructed `ContAction`,
and the right side uses the original actual bounded inverse algebra map.
The theorem `sectionAction_comp_baseMap` bundles the existing compatibility
on base sections as an equality of bounded algebra maps. Applying the
compatibility at `g⁻¹` proves `spectrumMap_smul`: the actual map from the
quotient spectrum to the base spectrum intertwines its local point action
with the original base point action. This equality does not require a
continuous-action object on the entire base spectrum.

Suppose `h : d ⟶ e` is an inclusion of actual rational loci and an element
`g : G` preserves both loci. The theorem `sectionAction_restriction` proves
that the actual bounded restriction `h.restriction : e.algebra → d.algebra`
commutes with the two forward section automorphisms. The proof uses the
published uniqueness theorem for bounded maps out of `e.algebra`:
the two composites agree on `e.baseMap`, by the structural-map
compatibilities and the restriction equation over the base. Applying this
identity at `g⁻¹` and evaluating seminorms proves
`spectrum_restriction_equivariant`. Thus the actual continuous spectrum map
from the smaller rational domain to the larger one is equivariant. Equal
loci with different rational presentations are allowed.

For an open subgroup `U` of `G`, the property `invariantRationalProperty ρ U`
selects exactly the rational data `d` for which
`U ≤ ρ.locusOpenSubgroup d`. The abbreviation
`InvariantRationalDomain ρ U` is the full subcategory of the existing
rational-locus inclusion category on those objects; it retains all
inclusions between their actual loci. The definition
`invariantStabilizerInclusion` is the continuous homomorphism from `U` to
the corresponding open locus stabilizer, given by the identity on ambient
group elements. Its continuity follows from the subtype topologies.

The definition `invariantSpectrum` restricts `spectrum ρ d` along this
homomorphism using Mathlib's `ContAction.res`. The functor
`invariantSpectrumFunctor ρ U` assigns these continuous `U`-actions to the
invariant rational data. On an inclusion it uses exactly the continuous
pullback induced by the published bounded restriction. Its equivariance
is the preceding theorem; its identity and composition laws follow from
the published restriction laws by evaluation of seminorms. The theorem
`invariantSpectrumFunctor_map_apply` states the map formula

```text
F(h)(x)(b) = x(h.restriction(b)).
```

Finally, `invariantSpectrumFunctor_forget` proves an equality of functors:
forgetting the actions is exactly the full inclusion into rational data
followed by the published `RationalData.toTopologicalSpace K P`.
It recovers the actual quotient spectra and restriction maps, not just
isomorphic replacements.

The module imports `NormContinuousAction` to reuse its
`topCatSelfForget` helper as a local instance. This is only the identity
forgetful functor on `TopCat`; it supplies no norm-continuity hypothesis
or result to the present construction.

The geometric motivation is Berkovich's unfinished *Etale equivariant
sheaves on p-adic analytic spaces* (1995–1996), section 1.1, printed/PDF
pp. 1–2. It defines continuous analytic actions by continuity into the
analytic automorphism group with its finite compact-domain spectral-function
tests, and defines equivariant morphisms of such spaces. The present
construction is an internal consequence of the Library's restricted
fixed-field, unit-radius rational-test topology, the actual rational
section actions, and the proved spectral local-continuity theorem.
The exact categorical functor is not a numbered theorem of the manuscript.

The underlying presented strict affinoid quotients and bounded maps follow
Berkovich's *Non-archimedean analytic spaces*, Trieste lectures (2009),
section 2.1 and Definition 2.1.2 on p. 7, Definition 2.1.11 on p. 8,
and Definition 2.2.1 and Exercise 2.2.2(ii) on p. 9. The restriction proof
uses the already implemented representing property of these actual
rational algebras.

The construction retains trivial valuations, zero or nonreduced quotients,
empty rational loci and empty spectra. It proves no equality between the
restricted topology and the full analytic automorphism topology, and no
identification of quotient and spectral norms. Arbitrary-radius domains,
analytic gluing, structure sheaves, analytic atlases, and equivariant etale
or quasi-etale sites remain separate work.

The registered Equish source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The Trieste source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
