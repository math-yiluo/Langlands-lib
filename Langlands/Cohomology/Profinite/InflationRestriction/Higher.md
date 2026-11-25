# Inflation–restriction in higher degree

`Langlands/Cohomology/Profinite/InflationRestriction/Higher.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a profinite group `G`, a closed normal subgroup `N` and a smooth `A` with `Hⁱ(N, A) = 0` for
`0 < i < q`: `0 → H^q(G/N, A^N) → H^q(G, A) → H^q(N, A)` is exact. The proof shifts dimension with
the coinduced module, whose `N`-invariants and restriction to `N` are acyclic.

## Declarations

- `homologyπ_zero_injective`, `exists_mem_invariants_map_eq`, `isIso_δ_of_isZero`: auxiliary facts
  on the long exact sequence.
- `infResShortComplex A N n`: the complex `H^{n+1}(G/N, A^N) → H^{n+1}(G, A) → H^{n+1}(N, A)`;
  `infResShortComplex_zero_mono_exact` (degree one), `shortExact_map_quotientToInvariants_coindShortComplex`,
  `infRes_step`, `infResShortComplex_mono_exact` (by induction on `n`).
- `infl_injective_of_isZero`: inflation `H^q(G/N, A^N) → H^q(G, A)` is injective;
  `range_infl_eq_ker_res`: its image is the kernel of restriction to `N`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/InflationRestriction/Higher.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are
the source's, with `cohomologyInfl_injective` → `infl_injective_of_isZero` and
`cohomologyInfl`/`cohomologyRes` → `infl`/`res`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §6, Proposition (1.6.7), second part, p. 67, proved by
  dimension shifting on p. 68.
