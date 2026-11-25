# The projection formula

`Langlands/Cohomology/Profinite/Cup/Corestriction.lean`, namespace `Langlands.ProfiniteCohomology`.

For an open subgroup `U` of a compact group: `cores(x ∪ res y) = cores(x) ∪ y`.

## Declarations

- `coindTensorRightFun`, `coindTensorLeftFun`, `coindTensorRight`, `coindTensorLeft`: the maps
  `Coind(A) ⊗ B → Coind(A ⊗ B)` (and on the left), with `coindTensorRight_comp_coindEvalOne`,
  `coindTensorRight_comp_coindTrace`; `isSmoothRep_coind_res_tensor_right`.
- `map_coeffMap`, `cohomologyMap_map`: composition of maps along homomorphisms with coefficient maps.
- `shapiroMap_inv_apply`, `inv_shapiroMap_apply`, `cores_shapiroMap`: corestriction through Shapiro.
- `cores_cup_res`: the projection formula.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CupProducts/Projection.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the
source's, with `cohomologyMapAlong_cohomologyMap` → `map_coeffMap`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, pp. 36–38 (cup products).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §5, Proposition (1.5.3)(iv), p. 49 (projection formula
  `cor(α ∪ res β) = (cor α) ∪ β` for an open subgroup).
