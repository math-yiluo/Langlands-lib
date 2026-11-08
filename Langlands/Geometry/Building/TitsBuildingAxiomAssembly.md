# The torus correspondence and KP Axiom 4.1.1 for the restricted Tits realization

This module completes the reduction of the building clause
`SatisfiesBuildingAxiom` of `RootValuationBuildingConstructionStatement` (KP
Axiom 4.1.1 for one group) for the restricted Tits realization. The
remaining inputs are explicit: the full supplied Tits comparison for the
literal affine Tits datum, normality of `G(F)^0` and of `N(F) ∩ G(F)^0`, and
two published statements, `SimplyConnectedCentralizerProductStatement` (KP
Fact 2.6.22) and `MaximalSplitTorusConjugacyStatement`. All results are
internal deductions from the imported definitions, the frozen candidates
`TitsRestrictedRealization` and `TitsNormalizerApartmentStabilizer`, and the
existing Library API `TorusTransporterOrbit`.

## Tori and their conjugates

For actual `B : ValuationBuildingData G`, `B.conjTorus g` is the existing
subgroup functor `range (i ≫ Int(g))`, that is `g S g⁻¹`.
`conjTorus_eq_smul_range` rewrites it as `g • range i` for the existing
conjugation action of rational points on subgroup functors
(`SubgroupFunctor.basePoint_smul_range`).

`conjTorus_eq_conjTorus_iff` proves that `g S g⁻¹ = h S h⁻¹` exactly when
`h⁻¹ g` lies in the actual normalizer points `normalizerPoints i`. Indeed,
`g • R = h • R` is equivalent to `(h⁻¹ g) • R = R`. The existing
`stabilizer_range_eq_normalizerPoints` identifies the stabilizer of the range
of `i` with `normalizerPoints i`.

## The torus correspondence

`conjTorus_eq_iff_of_normalizer` assumes the normalizer-stabilizer clause
`HasNormalizerApartmentStabilizer` and proves that `g S g⁻¹ = h S h⁻¹` exactly
when `g · A(S) = h · A(S)`. By the previous lemma the first condition means
`h⁻¹ g ∈ N(F)`. By the clause, this means that `h⁻¹ g` stabilizes `A(S)`.

`conjTorusApartmentEquiv` is the resulting bijection (KP Corollary 7.6.9). It
goes from the set of conjugates `g S g⁻¹` (the range of `conjTorus`) to the
apartments `g · A(S)` of `B(G)`. A conjugate torus is sent to `g · A(S)` for a
chosen `g` realizing it, and an apartment to `g S g⁻¹` for a chosen `g` with
`Y = g · A(S)`. The previous equivalence makes these choices irrelevant and
the two maps inverse. `conjTorusApartmentEquiv_apply` computes it on
`g S g⁻¹`.

`hasTorusApartmentCorrespondence` proves the existing structure
`HasTorusApartmentCorrespondence` from `MaximalSplitTorusConjugacyStatement`
and the normalizer-stabilizer clause. The chart clause is the existing
`exists_torusChart_of_maximalSplitTorusConjugacy`, and the second clause is
`conjTorus_eq_iff_of_normalizer`.

## The building clause

`satisfiesBuildingAxiom_affineTitsRealization_of_statements` takes actual
`P : ParahoricBuildingData G` with instances `[P.normalizerZero.Normal]` and
`[P.zeroSubgroup.Normal]`. It also takes an affine Weyl comparison
`e : P.affinePart ≃* affineWeylGroup P.affineRoots`, the corrected affine root
system hypothesis `hA`, and a chamber `Ca` of `A(S)`. The remaining inputs are
the full supplied `hT : P.IsBuildingTitsSystem Ca P.affineTitsProjection
(P.chamberSimpleInAffinePart e Ca)`, `hfact` and `hconj`. The normalizer
clause comes from `hasNormalizerApartmentStabilizer_of_simplyConnectedCentralizerProduct`
applied to `hfact`, and the torus clause from `hasTorusApartmentCorrespondence`.
The frozen `satisfiesBuildingAxiom_affineTitsRealization` then gives
`P.SatisfiesBuildingAxiom hT.titsRealization` for the restricted Tits
realization.

## Scope

This is a conditional assembly. The full Tits comparison `hT`, the two
normality instances and the two published statements are hypotheses, and
none of them is proved here. Actual valuation data for an arbitrary connected
reductive group are not constructed. The other conjuncts of
`RootValuationBuildingConstructionStatement` are not addressed, and the host
theorem is not proved.
