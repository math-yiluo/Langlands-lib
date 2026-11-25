# The five-term exact sequence

`Langlands/Cohomology/Profinite/InflationRestriction/FiveTerm.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a profinite group `G`, a closed normal subgroup `N` and a smooth `A`:
`0 → H¹(G/N, A^N) → H¹(G, A) → H¹(N, A)^G → H²(G/N, A^N) → H²(G, A)` is exact.

## Declarations

- `resInv A N`: restriction `H¹(G, A) → H¹(N, A)^G` (into the conjugation-invariant classes),
  `coe_resInv_apply`.
- `cocycleOneApply_cocyclesMap`, `res_π`, `isTgLift_cocycleOneApplyG`,
  `isLocallyConstant_cocycleOneApplyG`, `isTransgression_res`, `infl_tgClass`,
  `infl_transgression` (inflation kills transgressions), `transgression_resInv` (transgression
  kills restrictions), `exists_resInv_eq`, `comp_vecCons_mk`, `exists_transgression_eq`: exactness
  at each place.
- `fiveTerm_exact`: inflation in degree one is injective and the sequence is exact at
  `H¹(G, A)`, `H¹(N, A)^G` and `H²(G/N, A^N)`.
- `infRes_exact`: if `Hⁱ(N, A) = 0` for `0 < i < q`, then `0 → H^q(G/N, A^N) → H^q(G, A) → H^q(N, A)`
  is exact.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/InflationRestriction/FiveTerm.lean` and
`src/GroundTheory/ProfiniteCohomology/InflationRestriction.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's,
with `cohomologyInfl` → `infl`, `cohomologyRes` → `res`, `cohomologyInfl_injective` →
`infl_injective_of_isZero`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §6, Proposition (1.6.7), p. 67 (the five term exact sequence,
  and its form in degree `n` when `Hⁱ(H, A) = 0` for `0 < i < n`).
- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.6 b), p. 15 (the exact sequence in low dimensions).
