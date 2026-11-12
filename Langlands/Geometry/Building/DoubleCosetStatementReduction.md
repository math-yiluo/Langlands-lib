# The corrected KP Theorem 7.8.1(2),(3) from their structural inputs

This derived internal unit reduces the two published targets
`IwahoriDoubleCosetStatement` and `ParahoricDoubleCosetStatement` to three
published structural statements:

- `IwahoriWeylChamberSplittingStatement`, KP 7.8.2;
- `AffineIwahoriTitsStatement`, the `G(F)^0` branch of KP Theorem 7.5.3(1),(2);
- `FacetParabolicComparisonStatement`, the common-chamber form of KP
  Proposition 7.5.5.

Its proposition `DoubleCosetStatementReductionStatement` is the conjunction of
two implications between these published propositions, all at the same
universe `u`:

- the chamber splitting statement and the affine Iwahori–Tits statement
  together imply `IwahoriDoubleCosetStatement`;
- the chamber splitting statement and the facet-parabolic comparison statement
  together imply `ParahoricDoubleCosetStatement`.

The theorem `doubleCosetStatementReduction` proves it. The three structural
statements are explicit antecedents. This unit proves none of them. It also
does not prove either double-coset statement outright. The hypotheses of the
two targets are unchanged: the closing theorems
`iwahoriDoubleCosetStatement_of_statements` and
`parahoricDoubleCosetStatement_of_statements` instantiate the antecedents at
exactly the field, group, data, apartment-axiom, chamber and face premises of
the targets. The three antecedents use exactly the same premises.

## Fixed-data step

Fix actual data `P : ParahoricBuildingData G` over a nonarchimedean local field
with `P.normalizerZero` and `P.zeroSubgroup` normal (instance arguments).

The published `affineTitsProjection_coe` from
[`AffineIwahoriTits`](AffineIwahoriTits.md) supplies the compatibility hypothesis
of the component adapters directly. For every `n ∈ N(F) ∩ G(F)^0`, the literal
restricted quotient `P.affineTitsProjection n` has underlying element in
`P.IwahoriWeylGroup` equal to the full normalizer quotient class of `n`.
The normalizer comparison unfolds to the explicit representative used by the adapters.

`iwahoriDoubleCosetBijection_of_splitting_of_affineIwahoriTits` assumes
`P.IwahoriWeylChamberSplitting C` and `P.AffineIwahoriTits C`, and concludes
`P.IwahoriDoubleCosetBijection C`. It unpacks the affine Iwahori–Tits datum
`P.AffineIwahoriTitsWith C e`. That datum contains the containment
`P.parahoric C ≤ P.zeroSubgroup` of the generated full Iwahori subgroup and the
published `Langlands.Group.IsTitsSystem` for `P.parahoricInZero C`,
`P.normalizerInZero`, `P.affineTitsProjection` and the transported
chamber-simple reflections. The published lemma
`chamberStabilizer_toComponents_surjective_of_splitting` extracts, from the
splitting, surjectivity of `P.toComponents` on the full chamber stabilizer
`P.chamberStabilizer C`. The published adapter
`iwahoriDoubleCosetBijection_of_zeroTits` then takes the containment, the
compatibility above, the Tits system and this surjectivity, and gives the
equivalence `P.IwahoriWeylGroup ≃ P_C \ G(F) / P_C`. It sends the class of every
`n : normalizerPoints P.i` to `P_C n P_C`.

`parahoricDoubleCosetBijection_of_splitting_of_commonChamberFacetParabolics`
assumes `P.IwahoriWeylChamberSplitting C` and
`P.CommonChamberFacetParabolics C F₁ F₂`, and concludes
`P.ParahoricDoubleCosetBijection F₁ F₂`. The second hypothesis provides one
comparison `e`, one datum `P.AffineIwahoriTitsWith C e`, and the two comparisons
`P.FacetParabolicComparisonWith C Fᵢ e`. The published adapter
`parahoricDoubleCosetBijection_of_zeroTits_subgroupOf` receives:

- the chamber containment, the compatibility and the Tits system from that one
  datum;
- the component surjectivity from the splitting, as above;
- the generator sets `X = P.facetSimpleInAffinePart e C F₁` and
  `Y = P.facetSimpleInAffinePart e C F₂`, contained in the Tits generators by
  the published `facetSimpleInAffinePart_subset`;
- for each facet, the stabilizer equality `weyl_stabilizer` (read from right to
  left), the containment `parahoric_le_zero` and the subgroup-form Bruhat-cell
  comparison `parabolic_eq`.

The result is the equivalence between `W^aff_{F₁} \ W̃^0 / W^aff_{F₂}`, the
double-coset quotient of the full Iwahori–Weyl group by the existing setwise
affine facet stabilizers, and `P_{F₁} \ G(F) / P_{F₂}`. It sends the double coset
of the class of every actual normalizer element `n` to `P_{F₁} n P_{F₂}`.

Both equivalences retain all components of `P.IwahoriWeylGroup` and of
`G(F)`, and use the actual generated full parahorics.

## The corrected injectivity argument

The authors' corrections of 1 November 2024 (PDF page 35) state that the printed
injectivity proof of Theorem 7.8.1(2) is insufficient. The printed proof uses
only `I ∩ N(k) = Z(k)^0`. The replacement writes the two elements as
`w₁ρ₁`, `w₂ρ₂` with `wᵢ ∈ W_aff` and `ρᵢ` in the chamber stabilizer. It uses
Theorem 7.8.1(1) to get `ρ₁ = ρ₂`. These elements normalize `I`, so `w₁` and
`w₂` have the same image in `I \ G(k)^0 / I`. The Bruhat decomposition for the
Iwahori–Tits system of Theorem 7.5.3 then gives `w₁ = w₂`.

The adapters used here implement this route. The component surjectivity
extracted from the chamber splitting, together with the published covariance
of the generated parahorics under `N(F)`, supplies for every component a
chamber-stabilizer representative that normalizes the full Iwahori subgroup.
The component Bruhat construction compares components,
removes a common normalizing representative, and applies Bruhat uniqueness of
the actual Tits system in `G(F)^0`. No use is made of the bare equality
`I ∩ N(F) = Z(F)^0`.

## Provenance and scope

The provenance is derived. The proposition is an implication between published
Library statements. Its antecedents and conclusions are the source-backed
statements of `IwahoriWeylStatement`, `AffineIwahoriTitsStatement` and
`FacetParabolicComparisonStatement`, unchanged. The proofs are internal
assemblies of published adapters. The mathematical context is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Theorem 7.5.3 and Proposition 7.5.5
(PDF pages 292–293), and Theorem 7.8.1(2),(3) with §7.8.2 (PDF pages 303–304).
The corrected injectivity argument is from the authors' corrections of
1 November 2024, PDF page 35.

The three antecedent statements are open proof targets of tasks
`fc0c8f82-31e8-47dd-ac37-ab6bee878f46` (chamber splitting),
`20fbe465-f4ae-4fe9-9846-2201f1c31d28` (affine Iwahori–Tits) and
`c2766503-ffb3-4bf4-a441-5a73eca4fac3` (facet-parabolic comparison). Once they
are proved, `iwahoriDoubleCosetStatement_of_statements` and
`parahoricDoubleCosetStatement_of_statements` close the two targets with their
original hypotheses.
