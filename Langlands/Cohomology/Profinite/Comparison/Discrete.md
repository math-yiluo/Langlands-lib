# Comparison with the cohomology of an abstract group

`Langlands/Cohomology/Profinite/Comparison/Discrete.lean`, namespace `Langlands.ProfiniteCohomology`.

The locally constant cochains are a subcomplex of Mathlib's inhomogeneous cochains, so there is a
natural map from `cohomology A n` to Mathlib's `groupCohomology A n` (cohomology of `G` as an
abstract group). For a discrete group every cochain is locally constant, and the map is an
isomorphism: the cochain model agrees with Mathlib's group cohomology.

## Declarations

- `toGroupCohomology A n : cohomology A n ⟶ groupCohomology A n`, induced by `cochainsι A`.
- `map_comp_toGroupCohomology`: for `φ : H →ₜ* G` and `f : Rep.res φ A ⟶ B`,
  `map φ f n ≫ toGroupCohomology B n = toGroupCohomology A n ≫ groupCohomology.map φ f n`;
  `map_id_comp_toGroupCohomology`, `res_comp_toGroupCohomology`, `infl_comp_toGroupCohomology`:
  the cases of coefficient maps, restriction and inflation.
- `isIso_cochainsι`: for a discrete group the inclusion of complexes is an isomorphism.
- `isoGroupCohomology A n : cohomology A n ≅ groupCohomology A n` for a discrete group, with
  `isoGroupCohomology_hom`: its forward map is `toGroupCohomology A n`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean`
(section `Comparison`), `src/GroundTheory/ProfiniteCohomology/CohomologyFunctoriality.lean`
(`cohomologyMapAlong_comp_homologyMap_cochainsComplexι` and its restriction and inflation cases)
and `src/GroundTheory/ProfiniteCohomology/CohomologyFunctoriality/Naturality.lean` of the
repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Source names: `cohomologyToGroupCohomology` →
`toGroupCohomology`, `cohomologyIsoGroupCohomology` → `isoGroupCohomology`,
`cohomologyMapAlong_comp_homologyMap_cochainsComplexι` → `map_comp_toGroupCohomology`,
`cohomologyMap_comp_cohomologyToGroupCohomology` → `map_id_comp_toGroupCohomology`,
`cohomologyRes_comp_cohomologyToGroupCohomology` → `res_comp_toGroupCohomology`,
`cohomologyInfl_comp_cohomologyToGroupCohomology` → `infl_comp_toGroupCohomology`,
`isIso_cochainsComplexι` → `isIso_cochainsι`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §2, Definition (1.2.2), p. 13, and inhomogeneous cochains,
  p. 14. Neukirch–Schmidt–Wingberg work with profinite groups and do not state this comparison.
