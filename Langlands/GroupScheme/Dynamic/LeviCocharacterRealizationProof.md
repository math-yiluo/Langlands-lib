# Simultaneous dynamic realization of extension from a Levi

Authors: Worker 1280 and Worker 1068.

`Langlands.GroupScheme.dynamicLeviCocharacterRealization` proves exactly the
published proposition `DynamicLeviCocharacterRealizationStatement.{u}`.
For every field in the arbitrary universe `u`, every connected reductive
group scheme `G`, every cocharacter `χ`, every closed representative
`j : L → G` of its dynamic centralizer, and every cocharacter `ν` of `L`,
it constructs an ambient cocharacter `ψ` with the three equalities

- `Dynamic.parabolic ψ =
  Dynamic.extendFromCentralizer χ j hj (Dynamic.parabolic ν)`;
- `Dynamic.centralizer ψ = (Dynamic.centralizer ν).map j`;
- `Dynamic.unipotent ψ =
  Dynamic.extendFromCentralizer χ j hj (Dynamic.unipotent ν)`.

These are equalities of the actual subgroup functors. The extensions are the
defined literal two-factor products on each original test scheme. Every test
scheme is included, with no reducedness or affineness restriction. The theorem
has no assumptions beyond those in the published proposition.

## Implemented proof

Connected reductivity supplies smoothness and affineness of the structure
morphism; smoothness supplies local finite type and affineness supplies
separatedness. By `Dynamic.range_comp_le_centralizer`, the ambient
cocharacter `tau = ν ≫ j` has its range in the dynamic centralizer of `χ`.
The theorem `Dynamic.exists_dominant_inclusions` supplies a natural bound
`N` such that a combination `χ(tⁿ) tau(t)` for `n ≥ N` has its parabolic
inside that of `χ`, its unipotent functor containing that of `χ`, and its
centralizer inside that of `χ`.

Use `Dynamic.cocharacterCombination` with `n = N` to construct `ψ` as an
actual group-scheme morphism. Its point formula is
`Dynamic.comp_cocharacterCombination`, so the three inclusions apply at
`n = N`. Finally,
`Dynamic.realization_cocharacterCombination_of_inclusions` turns those
inclusions into all three displayed equalities.

The latter reduction uses dynamic limits and the closed representative to
lift the centralizer factor on the original test. The dominant-inclusions
theorem uses finitely many bihomogeneous coordinate generators and a bound
on their second weights, then lifts its affine tests to all schemes.
Their detailed implementations are documented in the imported modules
`Dynamic.LeviCocharacterCombination`, `Dynamic.DominantCombinationInclusions`
and `Dynamic.AffineInclusionCriterion`.

## Provenance

This is the assembly proof of the Library's derived simultaneous realization
target. Its mathematical scope and source motivation are those documented in
the unchanged paired Markdown of
`Rational.DynamicLeviCocharacterRealizationStatement`; no new literature
assertion is made. Worker 1280 supplied the commuting combination,
exact-product reduction, affine-test lifting and final assembly.
Worker 1068 supplied the dominant-inclusions proof.
