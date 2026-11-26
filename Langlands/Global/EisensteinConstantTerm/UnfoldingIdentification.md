# The geometric-lemma parabolics as dynamic parabolics

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingIdentification`, namespace
`Langlands.Global`.

## Helpers

- `carrier_range_comp_innerIso_inv`: the rational points of `j ≫ (G.innerIso w).inv` are the
  conjugate by `w⁻¹` of those of `j`.
- `principalPoint_injective`, `map_conj_map_principalPoint`: the principal map from rational
  points to adelic points is injective and intertwines conjugations.
- `hasDenseRationalPoints_of_closedSubgroup`, `range_eq_of_carrier_eq`: over an infinite perfect
  field, two closed smooth connected subgroups with the same rational points are equal. Rational
  points are dense by the Library's unirationality theorem `connectedGroupUnirationality`, and
  `range_le_of_dense_rationalPoints` applies in both directions.

## Main result

`exists_dynamic_unfolding_data`: let `G` be connected reductive over a number field, with
parabolics `p`, `q`, `f ≫ p`, `g' ≫ q`, geometric unipotent radicals `iU`, `iV`, `iU'`, `iV'`, and
`IsGeometricLemmaDatum p iU q iV f g' w`. Write `e = G.innerIso w`. There are cocharacters
`χ`, `τ`, `ψ`, `θ` of `G` with `IsCommutingRefinement χ τ ψ`, `IsCommutingRefinement τ χ θ`,
`U(τ) ∩ P(χ) ≤ U(ψ)`, and, as subgroup functors,
`range p = P(χ)`, `range (iU ≫ p) = U(χ)`, `range (q ≫ e.inv) = P(τ)`,
`range (iV ≫ q ≫ e.inv) = U(τ)`, `range (f ≫ p) = P(ψ)`, `range (iU' ≫ f ≫ p) = U(ψ)`,
`range (g' ≫ q ≫ e.inv) = P(θ)` and `range (iV' ≫ g' ≫ q ≫ e.inv) = U(θ)`.

## Proof

`P` and `w⁻¹ Q w` contain a common maximal split torus `S` (`parabolicIntersectionSplitTorus`),
so they are `P(χ)` and `P(τ)` for cocharacters `χ`, `τ` of `S`
(`IsParabolicSubgroup.exists_cocharacter_of_maximalSplitTorus`); these commute. The radicals are
the identity-limit subgroups (`radical_range_eq_dynamic_unipotent`). The commuting refinements
`ψ`, `θ` exist by `exists_common_levi_refinements`. The rational points of `P'` are
`(P(F) ∩ w⁻¹ Q(F) w) U(F)` by the datum and the injectivity of the principal map, which are the
rational points of `P(ψ)` by `parabolic_refinement_eq_sup`; both are closed, smooth and connected
(dynamic parabolics by the Library's `dynamicSmooth` and `dynamicConnected`), so
`range (f ≫ p) = P(ψ)` by `range_eq_of_carrier_eq`. The same argument conjugated by `w⁻¹` gives
`w⁻¹ Q' w = P(θ)`. The radicals of `P'` and `w⁻¹ Q' w` are then `U(ψ)` and `U(θ)`.

## Provenance

This realizes the identification of `P'`, `Q'` with Bernstein–Lapid's `P_w`, `Q_w` (Lemma 6.7 (2),
journal p. 207) through rational points, as described in the Markdown of
`GeometricLemmaUnfoldingStatement`.
