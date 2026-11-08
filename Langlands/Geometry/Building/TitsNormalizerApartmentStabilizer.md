# The stabilizer of the apartment of `S` under the Tits comparison

Fix actual `P : ParahoricBuildingData G` over a nonarchimedean local field at
universe `u`, and the full supplied comparison
`hT : P.IsBuildingTitsSystem Ca π Sgen` (KP Axiom 4.1.9), where `Ca` is a
facet of the apartment `A(S)` (`hCa : AffineRootSystem.IsFacet P.affineRoots Ca`;
in the axiom it is a chamber). This module proves the normalizer-stabilizer
clause `HasNormalizerApartmentStabilizer` of KP Axiom 4.1.1: the stabilizer of
`A(S)` in `G(F)` is `N(F)`. This is the first claim of KP Proposition 7.6.8.
Following the proof of KP Proposition 7.6.8 (book p. 266), the argument has
two steps. Inside `G(F)^0`, the stabilizer of the apartment is
`N(F) ∩ G(F)^0`. KP's proof attributes this to Proposition 1.5.13, whose
printed statement does not contain it; here it comes from the frozen
`TitsApartmentStabilizer` candidate, which proves it from Bruhat disjointness
and saturation. The decomposition `G(F) = G(F)^0 N(F)`, a consequence of KP
Fact 2.6.22, then passes to `G(F)`. All results are internal
deductions from the imported definitions and proved APIs. The decomposition
is a hypothesis.

## The standard apartment

`chamberFacet hCa` is the original quotient facet `apartmentMap '' Ca`. Its
stabilizer in `G(F)^0` is, by definition, the Borel subgroup
`P.chamberZeroStabilizerIn Ca` of the Tits system.

`facetStabilizersIn_apartmentImage` proves that the stabilizers in `G(F)^0` of
the facets contained in `A(S)` (the existing `P.facetStabilizersIn`) form the
standard restricted apartment `restrictedApartment … 1`. By
`hT.apartmentFacetStabilizers_eq`, this set is some restricted apartment. For
each `m ∈ N(F) ∩ G(F)^0`, the translate of `chamberFacet hCa` by `m` lies in
`A(S)`, because `N(F)` acts on the image of the apartment through its action
on `A(S)` (existing `normalizer_smul_apartmentMap`). Its stabilizer is
`m B m⁻¹` (existing `facetZeroStabilizer_zeroFacetTranslate`). Thus the
apartment contains every chamber of the standard apartment. Since the Tits
system is saturated (`hT.isSaturated`), `restrictedApartment_eq_one_of_forall`
identifies it with the standard apartment.

`mem_normalizerPoints_of_smul_apartmentImage`: let `g ∈ G(F)^0` with
`g · A(S) = A(S)`. The existing `facetStabilizersIn_smul` and
`image_conjugateSubgroup_restrictedApartment` show that the facet stabilizers
in `g · A(S)` form the restricted apartment based at `g`. Hence that apartment
is the standard one. By `mem_normalizer_of_restrictedApartment_eq`, `g`
belongs to `N(F) ∩ G(F)^0`, so `g ∈ N(F)`.

## Passage to `G(F)`

`hasNormalizerApartmentStabilizer` assumes
`hprod : ∀ g, ∃ k ∈ G(F)^0, ∃ n ∈ N(F), g = k n`. For `g` stabilizing `A(S)`,
write `g = k n`. Since `n` stabilizes `A(S)` (existing
`normalizerPoints_le_stabilizer_apartmentImage`), so does `k`. Hence
`k ∈ N(F)` and `g ∈ N(F)`. The existing `hasNormalizerApartmentStabilizer_iff`
concludes.

`exists_zero_mul_normalizer` derives `hprod` from the published statement
`SimplyConnectedCentralizerProductStatement` (KP Fact 2.6.22 for the minimal
Levi subgroup `Z_G(S)`). It applies the statement to the simply connected cover
and centralizer recorded in `P.zeroDatum` and `P.centralizer`. The resulting
factor in `G(F)^♮` lies in `G(F)^0` (existing
`simplyConnectedImage_le_zeroSubgroup`). The factor `j(z)` lies in `N(F)`,
because centralizing points normalize (existing `map_mem_centralizerPoints`,
`centralizerPoints_le_normalizerPoints`).
`hasNormalizerApartmentStabilizer_of_simplyConnectedCentralizerProduct`
combines the two.

## Scope

The results depend on the supplied full Tits comparison `hT` and on the facet
`Ca`. The final corollary also depends on
`SimplyConnectedCentralizerProductStatement`, which is used as a hypothesis
and is not proved here. The second claim of KP Proposition 7.6.8, the torus
correspondence of Corollary 7.6.9 and the existence of actual data for
arbitrary `G` are not addressed. Nothing here proves
`RootValuationBuildingConstructionStatement`.
