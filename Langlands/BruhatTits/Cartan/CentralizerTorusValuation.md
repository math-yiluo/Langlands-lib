# Restricting the centralizer valuation to the actual torus

This internal definition unit connects the normalized valuation on actual
centralizer points to the valuation on actual torus points. It uses the
published positive character normalization and character-restriction laws.
It constructs no apartment action or geometric subgroup.

Let `F` be any nonarchimedean local field, with no characteristic restriction,
`S` a commutative group scheme, `Z` a group scheme, and `s : S.toGrp ⟶ Z`
an actual homomorphism. As in `CentralizerValuation`, the displayed argument
`h` is bijectivity of the actual `restrictionEvaluation s`; it contains no
building, reductivity or decomposition certificate. Applications to a maximal
split torus in its represented algebraic centralizer impose those geometric
hypotheses separately.

`torusValuationRestriction s h` is the composite of `rationalPoints.map s`
with `centralizerValuation s h`, with values in the multiplicative notation
for `V(S)`. Its specification evaluates a restricted character on this value
as the positive integer order of that pulled-back character at the original
torus point. The proof combines `centralizerValuation_spec` with the existing
`rationalCharacterValuation_characterRestrict`.

`torusValuationRestriction_eq_id` compares this map to the torus's own
normalized valuation, given the torus's identity comparison `hS`. This law
works for the same arbitrary `S` as the definition. The proof applies
normalization uniqueness for `s`, then evaluates the identity-normalized
torus valuation on each pulled-back character. It does not assert the
existence of `hS`.

For the coordinate split torus
`𝕋 = splitTorus.commGroupScheme (Spec F) I`, with finite `I`,
`torusValuationRestriction_eq_split` identifies this map with the published
`SplitTorusValuation.realValuation F I`. This equality needs `h` for `s`
but no additional identity comparison. It follows directly from the split
valuation's character-evaluation formula, the character-lattice equivalence,
and normalization uniqueness. `torusValuationRestriction_uniformizer`
then evaluates the map on an actual cocharacter at the chosen order-one
uniformizer: its value is `1 ⊗ c`, with positive sign. Empty `I` is allowed
and requires no separate argument.

The provenance is internal: the definition is composition of published maps,
and the laws follow from their normalization and naturality. Source
conventions agree with Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), §2.5(b), printed pp.88–89/PDF119–120, and §2.6(d),
printed pp.102–103/PDF133–134, with the positive valuation correction in
*Corrections and additions*, 1 November 2024, PDF24–25. These passages
motivate the normalization; no new source theorem is asserted here.

This unit supplies a torus normalization comparison for later full V 6
interfaces. It does not identify an apartment translation with the positive
valuation: the corrected translation comparison uses its negative projection
to the effective translation space. Full V 6, existence of actual building
data, the actual `Z(F)^0` and parahoric `P_x`, and the shared maximal compact
`K0` comparisons remain separate obligations. The coordinate split-torus law
does not discharge any general reductive-group Cartan statement.
