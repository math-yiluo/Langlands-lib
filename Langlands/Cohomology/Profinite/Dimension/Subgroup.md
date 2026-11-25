# Cohomological dimension of closed subgroups

`Langlands/Cohomology/Profinite/Dimension/Subgroup.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a closed subgroup `H` of a profinite group `G`, `cd p H ≤ cd p G`, with equality when `p`
does not divide the supernatural index of `H`; in particular a pro-`p` Sylow subgroup has the
same `p`-cohomological dimension as `G`.

## Declarations

Open subgroups.

- `isAddTorsion_coind`: the module coinduced from a torsion module of an open subgroup is
  torsion.
- `cd_openSubgroup_le`: for an open subgroup `U` of a compact group, `cd p U ≤ cd p G` (by
  Shapiro's lemma).

Cochains of `H ⊔ V` extended from `H`, for `V` normal (used to pass from a closed subgroup to
the open subgroups containing it).

- `inv_mul_mem_trans`, `inv_mul_mem_symm`, `inv_mul_mem_mul`, `inv_mul_mem_contractNth`:
  congruence modulo `V`. `exists_mem_inv_mul_mem`, `supSection H V` (a choice of an element of
  `H` congruent modulo `V` to a given element of `H ⊔ V`) and `supSection_spec`.
- `ConstOnCosets V c`: a cochain on `H` constant on congruence classes modulo `V`;
  `supExtend V c`: its extension to `H ⊔ V`, with `supExtend_eq`, `supExtend_inclusion`,
  `isLocallyConstant_supExtend` (for `V` open) and `d_supExtend` (extension commutes with the
  differential when `V` fixes the values); `constOnCosets_mono`.
- `exists_openNormalSubgroup_constOnCosets`: a locally constant cochain on a closed subgroup is
  constant modulo some open normal subgroup that fixes its values.
- `exists_resOfLE_eq`: every class of `Hᵠ(H, M)` (`H` closed) is the restriction of a class of
  `Hᵠ(U, M)` for some open `U ⊇ H`; `exists_res_eq_zero`: a class of `H^{q+1}(G, M)` vanishing on
  `H` already vanishes on some open `U ⊇ H`.

Closed subgroups.

- `cd_le_cd_closedSubgroup`: if `p` does not divide the supernatural index of the closed
  subgroup `H`, then `cd p G ≤ cd p H` (restriction to `H` is injective on `p`-primary classes).
- `finite_of_isSimpleOrder`: a simple smooth module killed by `p` over a profinite group is
  finite.
- `coindFixed H V A`, `coindFixedRep H V A`: the vectors of the module coinduced from `H` to `G`
  fixed by `V`, as a smooth `G`-module (`isSmoothRep_coindFixedRep` for `V` open);
  `coindFixedEval`: evaluation at `1`, a morphism of `H`-modules to `A`. `rho_eq_of_inv_mul_mem`,
  `summandFun` and its lemmas, `summandMap`, `summandMap_comp_coindFixedEval`: when `V ∩ H` acts
  trivially on `A`, `A` is a direct summand of the restriction of `coindFixedRep H V A` to `H`.
- `cd_closedSubgroup_le`: for a closed subgroup `H` of a profinite group,
  `cd p H ≤ cd p G`.
- `cd_closedSubgroup_eq`: equality when `p` does not divide the supernatural index of `H`;
  `cd_eq_of_isProSylow`: `cd p P = cd p G` for a pro-Sylow subgroup `P`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/CohomologicalDimension/CdpOpenSubgroupLe.lean`,
`src/GroundTheory/ProfiniteCohomology/CohomologicalDimension/Closed.lean` and
`src/GroundTheory/ProfiniteCohomology/CohomologicalDimension/Subgroup.lean`. The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's with `cdp` → `cd`
(`cdp_openSubgroup_le` → `cd_openSubgroup_le`, `cdp_le_cdp_closedSubgroup` →
`cd_le_cd_closedSubgroup`, `cdp_closedSubgroup_le` → `cd_closedSubgroup_le`,
`cdp_closedSubgroup_eq` → `cd_closedSubgroup_eq`, `cdp_eq_of_isProSylow` → `cd_eq_of_isProSylow`),
`cohomologyResLE`/`cohomologyRes` → `resOfLE`/`res` (`exists_cohomologyResLE_eq` →
`exists_resOfLE_eq`, `exists_cohomologyRes_eq_zero` → `exists_res_eq_zero`) and
`isDiscreteRep_coindFixedRep` → `isSmoothRep_coindFixedRep`.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §3.3, Proposition 14, p. 19 (`cd_p(H) ≤ cd_p(G)`, with
  equality if `(G : H)` is prime to `p`, or if `H` is open and `cd_p(G) < ∞`), and Corollary 1,
  p. 19 (Sylow subgroups).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §3, Proposition (3.3.5) and Corollary (3.3.6), p. 174.
