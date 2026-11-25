# Duality for groups with a dualizing datum

`Langlands/Cohomology/Profinite/Duality/Main.lean`, namespace `Langlands.ProfiniteCohomology`.

Let `G` be a compact group with a dualizing datum `H : DualizingData n D` (`DualModule.lean`).
Then for every open subgroup `U`, every finite smooth `U`-module `M` killed by `n` and
`r + s = 2`, the duality map

`Hʳ(U, M) → Hom(Hˢ(U, Hom(M, D)), ℤ/n)`, `x ↦ (y ↦ t_U(x ∪ y))`,

is bijective; in particular for `G` itself (with `t = t_⊤ ∘ res`). This is the abstract form of
Tate's local duality theorem (for `G` the absolute Galois group of a local field and
`D = μ_n`) and of Poincaré duality for profinite groups of dimension `2`; the local theory
provides the dualizing datum.

## Declarations

- `bijective_map_of_mulEquiv`: a topological isomorphism with mutually inverse coefficient maps
  induces bijections on cohomology.
- `exists_eq_openSubgroupOf`: an open subgroup of an open subgroup `U` is `openSubgroupOf U V`
  for some open `V ≤ U`.
- `DualizingData.fromSubgroupOf hVU C m`: the identification of `Hᵐ(V ∩ U, C)` (as a subgroup of
  `U`) with `Hᵐ(V, C)` (`bijective_fromSubgroupOf`); `t_cores_openSubgroupOf`,
  `bijective_t_cores_openSubgroupOf`.
- `DualizingData.zmodSubgroupOfHom`, `zmodSubgroupOfInvHom`, `bijective_zmodFromSubgroupOf`,
  `resFunctor_map_zmodMulPairing_comp`, `fromSubgroupOf_cupPairing` (compatibility of the
  identification with cup products), `isPerfectPairing_openSubgroupOf`.
- `DualizingData.groupDualityHypotheses U`: the restriction of the datum to an open subgroup
  `U` satisfies the hypotheses `GroupDualityHypotheses` of the dévissage, for `t_U`.
- Instance `DualizingData.isSmoothRep_dualRep_res`.
- `DualizingData.dualityMap_bijective H U M hM h`: the duality map for `U` and `M` is bijective.
- `topOpenSubgroupEquiv` (the subgroup `⊤` and `G`), `continuous_topOpenSubgroupEquiv`,
  `continuous_topOpenSubgroupEquiv_symm`, `bijective_res_top`,
  `resTensorIso_inv_comp_resFunctor_map_evalPairing`.
- `DualizingData.tTop H : H²(G, D) → ℤ/n` and `DualizingData.dualityMap_bijective_of_group`:
  the duality map for `G` itself is bijective.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/PoincareDuality.lean` of the repository
`leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names: `DualityHypotheses` → `DualizingData`,
`bijective_dualityMap` → `DualizingData.dualityMap_bijective`, `bijective_dualityMap_of_group` →
`DualizingData.dualityMap_bijective_of_group`, `bijective_cohomologyMapAlong_of_mulEquiv` →
`bijective_map_of_mulEquiv`; the other names are the source's. The statement of
`resFunctor_map_zmodMulPairing_comp` writes the coercion of the bundled homomorphism explicitly.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §3.5, pp. 24–26 (dualizing modules; Proposition 18, p. 25:
  the dualizing module of `G` is that of every open subgroup), and chapter II, §5.2, Theorem 2,
  p. 91 (Tate's local duality theorem).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §4, Theorem (3.4.1), p. 182, and Duality Theorem (3.4.6),
  p. 186 (dualizing modules, duality groups), and §7, Definition (3.7.1), p. 210 (Poincaré groups).
