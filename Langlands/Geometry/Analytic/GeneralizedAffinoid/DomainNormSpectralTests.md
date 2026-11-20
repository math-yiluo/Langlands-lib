# Spectral tests on full represented domains from norm-continuous orbits

Author: Worker 383.

This internal supporting module extends the rational-chart result
`RationalChart.normDomainSpectralSubgroup_mem_nhds` (module
`RationalNormSectionContinuity`) from rational charts to arbitrary full
represented affinoid domains. All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism`.

## Setting

`K : Type u` is a complete ultrametric normed field and
`A : PresentedAffinoidAlgebra K` is an actual finite positive-polyradius affinoid
quotient. `G : Type v` is a topological group and `ρ : G →* Aut A` is a group
homomorphism into the bounded automorphisms of `A`. The hypothesis `hρ` says that
every forward orbit `g ↦ (ρ g).hom a` is continuous for the quotient norm of `A`.

## Statements

- `locus_eq_iUnion_of_cover`: if finitely many rational charts `D k` of `A` have
  actual domain restrictions `(D k).toDomain ⟶ U` and their loci cover `U.locus`,
  then `U.locus` is the union of the loci `(D k).locus`. One inclusion is the
  covering hypothesis, the other is `Domain.Inclusion.subset`.
- `domainSpectralSubgroup_mem_nhds_of_normContinuous`: for every
  `U : Domain K A`, every section `b : U.algebra` and every `r > 0`, the inverse
  image under `ρ` of the single spectral test subgroup
  `domainSpectralSubgroup U b r` is a neighbourhood of `1` in `G`. By the
  membership criterion `mem_domainSpectralSubgroup`, this means: for `g` near `1`,
  `ρ g` preserves `U.locus` setwise and every point `x` of the Banach spectrum of
  `U.algebra` satisfies `x(σ_g(b) − b) ≤ r`, where `σ_g` is the constructed
  section operator `stabilizerSectionAction U` of `ρ g`.

## Proof

The published Gerritzen–Grauert type theorem `Domain.finiteRationalCover`
supplies rational charts `D 0, …, D (n−1)` of `A`, restrictions
`ι k : (D k).toDomain ⟶ U`, and the covering of `U.locus` by their loci. For each
`k`, `RationalChart.normDomainSpectralSubgroup_mem_nhds` makes the inverse image
of the test subgroup of `(D k).toDomain` with the restricted section
`(ι k).restriction b` and radius `r` a neighbourhood of `1`; the finite
intersection of these neighbourhoods is again one (`Filter.iInter_mem`).

Fix `g` in this intersection. For each `k` the membership criterion gives that
`ρ g` preserves `(D k).locus` and bounds the displacement of
`(ι k).restriction b` by `r` on the spectrum of `(D k).algebra`.

1. Stabilization. By `locus_eq_iUnion_of_cover`, `U.locus = ⋃ k, (D k).locus`.
   The image of a union is the union of the images, so `ρ g` preserves
   `U.locus`.
2. Bound. Let `x` be a point of the spectrum of `U.algebra`. Its structural image
   `U.spectrumMap x` lies in `U.locus` (`Represents.hasImageIn`), hence in some
   `(D k).locus`, which is the range of `(D k).toDomain.spectrumMap` (the range
   clause of `Represents`). Choose `x'` with
   `(D k).toDomain.spectrumMap x' = U.spectrumMap x`. The point
   `(ι k).spectrumMap x'` of the spectrum of `U.algebra` has the same structural
   image (`Domain.Inclusion.spectrumMap_over_base`), so it equals `x` by
   injectivity of `U.spectrumMap`, which is part of the published closed
   embedding theorem `Domain.spectrumEmbedding`. Thus `x(c) = x'((ι k).restriction c)`
   for every section `c`. The published identity
   `stabilizerSectionMap_restriction` says that restriction commutes with the two
   section operators of `ρ g`, so
   `(ι k).restriction (σ_g(b) − b) = σ^k_g((ι k).restriction b) − (ι k).restriction b`,
   and the bound for `D k` gives `x(σ_g(b) − b) ≤ r`.

## Provenance and scope

This is an internal derived result assembled from published Library theorems:
`finiteRationalCover`, `spectrumEmbedding`, `normDomainSpectralSubgroup_mem_nhds`,
`stabilizerSectionMap_restriction` and the domain representation API. It is used
by `DrinfeldActionContinuityProof` for the arbitrary affinoid domains of the
saturated atlas of Drinfeld's upper half space. It asserts no continuity into a
global automorphism topology and no statement for infinite families of tests.
