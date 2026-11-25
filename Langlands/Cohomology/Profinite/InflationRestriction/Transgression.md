# Transgression

`Langlands/Cohomology/Profinite/InflationRestriction/Transgression.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a profinite group `G`, a closed normal subgroup `N` and a smooth `A`, the transgression
`tg : H¹(N, A)^{G} → H²(G/N, A^N)`: a `G`-invariant class of `H¹(N, A)` is represented by a
cocycle `x` that extends to a locally constant map `y : G → A` (`IsTgLift`) whose coboundary
descends to a `2`-cocycle of `G/N` with values in `A^N`.

## Declarations

- `tgDiff`, `IsCocycleOne`, `IsTgLift` and its lemmas (`mul_left`, `tgDiff_mul_right`,
  `tgDiff_mul_left`, `tgDiff_mem_invariants`, `tgDiff_mul_mul`, `tgDiff_out`, `add`, `smul`): the
  extension of a cocycle of `N` to `G` and its coboundary.
- `liftCochain`, `isLocallyConstant_tgDiff`, `cochains_d_liftCochain`, `tgCochain`, `tgCochain_d`,
  `cochainsMap_mk_injective`, `cochainsMap_tgCochain`, `cochains_d_d_apply`: the descended
  cochain of `G/N`.
- `cocycleOf`, `iCycles_cocycleOf`, `cocycleOf_eq_iff`, `cohomologyπ_cocycleOf_eq`: cocycles from
  cochains with zero differential.
- `isCocycleOne_cocycleOneApply`, `tgClass`, `tgClass_eq` (independent of choices), `tgClass_add`,
  `tgClass_smul`, `cocycleOneApply_add`, `cocycleOneApply_smul`.
- `IsTransgression`, `IsTransgression.unique`, `.add`, `.smul`; `exists_isTgLift` (a locally
  constant extension exists, using a continuous section of `G → G/N`),
  `exists_isTransgression`.
- `transgression A N hN`: the `k`-linear map `H¹(N, A)^G → H²(G/N, A^N)`;
  `isTransgression_transgression`, `transgression_eq_iff`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/InflationRestriction/TransgressionLift.lean` and
`InflationRestriction/Transgression.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §6, Proposition (1.6.6), p. 65 (transgression
  `tg : H¹(H, A)^{G/H} → H²(G/H, A^H)`, defined by an extension `y` of the cocycle whose coboundary
  descends to `G/H`; the continuous section of `G → G/H` comes from exercise 4 of §1).
