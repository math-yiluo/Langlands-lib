# The unfolding identity from the subgroup structure

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingReduction`, namespace
`Langlands.Global`.

## Result

`geometricLemmaUnfolding_of_structure`: take the data and instances of
`GeometricLemmaUnfoldingStatement`, the four geometric unipotent radical hypotheses and
`UnfoldingSubgroupStructure F p iU q iV w f iU' g' iV'`. For every measurable `h` left invariant
under `U(𝔸)` and `P(F)`, and every `y`, if `∫⁻ ‖h(w⁻¹ v̄ y)‖` against `stabilizerMeasure` is finite,
then `x ↦ subgroupConstantTerm F (iU' ≫ f ≫ p) h (w⁻¹ x̄ y)` is integrable for
`intertwiningMeasure F (f ≫ p) iU' (iV' ≫ g' ≫ q) w`, with the same integral. This is the
conclusion of `GeometricLemmaUnfoldingStatement`.

## Proof

The ambient group is `G(𝔸)` with the discrete subgroup `G(F)`. The rational lattices of the
adelic radicals are their intersections with `G(F)` (`rationalSubgroup_range_eq_latticeOf`), and
the Library's normalized measures are the normalized Haar measures `normalizedHaar` of these
lattices (`normalizedHaarMeasure_eq_normalizedHaar`). Compact covers come from the compactness
of the rational quotients of smooth connected unipotent groups and of the stabilizers.

The two discrete groups of the statement are identified with the abstract ones:
`stabilizerRationalSubgroup = V ∩ G(F) ∩ w U'(𝔸) w⁻¹` by item 1 of the structure and the
inclusion `U'(F) ⊆ P(F)`, and `intertwiningRationalSubgroup = V' ∩ G(F) ∩ w U'(𝔸) w⁻¹` by
definition. The quotient integrals with chosen representatives become fundamental-domain
integrals (`integral_discreteQuotientMeasure_out` and its companions), the constant term becomes
a fundamental-domain average (`subgroupConstantTerm_eq_setIntegral`), and
`integral_unfolding_eq` applies.
