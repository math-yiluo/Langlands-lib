# Pro-`p` groups and pro-Sylow subgroups

`Langlands/Cohomology/Profinite/Dimension/ProP.lean`, namespace `Langlands.ProfiniteCohomology`.

A topological group is pro-`p` if all its finite quotients by open normal subgroups are
`p`-groups. A pro-Sylow (`p`-Sylow) subgroup of a profinite group is a closed pro-`p` subgroup
whose supernatural index is prime to `p`. They exist, and every pro-`p` subgroup lies in one.

## Declarations

- `IsProPGroup p G`: every quotient `G ⧸ U` by an open normal subgroup is a `p`-group.
  `isProPGroup_iff`: equivalently, for every `U` and `g`, some `g^{p^k}` lies in `U`.
- `isPGroup_map_mk_iff`: the image of `H` in `G ⧸ U` is a `p`-group iff every `h ∈ H` has a
  `p`-power in `U`.
- For a compact totally disconnected group: `exists_subgroupOf_le` (every open normal subgroup
  of a subgroup `H` contains the trace on `H` of an open normal subgroup of `G`),
  `isProPGroup_subgroup_iff`, `isProPGroup_subgroup_iff_isPGroup_map` (a subgroup is pro-`p` iff
  its images in all finite quotients are `p`-groups), `IsProPGroup.of_le` (subgroups of pro-`p`
  subgroups are pro-`p`), `isProPGroup_bot`.
- `sup_eq_comap_map`, `index_sup_eq_index_map`: `H U` is the preimage of the image of `H` in
  `G ⧸ U`, of the same index.
- `quotMap h`: for `U ≤ V`, the projection `G ⧸ U → G ⧸ V`, with `quotMap_comp_mk'`,
  `quotMap_surjective`, `quotMap_self`, `quotMap_comp`, `map_map_quotMap`.
- `IsProSylow p P`: `P` is closed, pro-`p`, and `p` does not divide its supernatural index.
- `not_dvd_superIndex_iff_map`: `p` does not divide the supernatural index of `H` iff it divides
  the index of no image of `H` in a finite quotient. `isProSylow_iff`: a closed `P` is
  pro-Sylow iff all its images in finite quotients are Sylow subgroups;
  `IsProSylow.toSylow U` is that Sylow subgroup of `G ⧸ U` (`IsProSylow.coe_toSylow`).
- `sylowSystem p H`: the functor on open normal subgroups sending `U` to the Sylow subgroups
  of `G ⧸ U` containing the image of `H` (an inverse system of nonempty finite sets).
- `exists_isProSylow_le`: in a profinite group every pro-`p` subgroup is contained in a
  pro-Sylow subgroup; `exists_isProSylow`: pro-Sylow subgroups exist.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean` and
`src/GroundTheory/ProfiniteCohomology/NotDvdSuperIndexIffMap.lean`. The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §1.4, pp. 6–7 (pro-`p`-groups and Sylow `p`-subgroups, p. 6;
  Proposition 3, existence, and Proposition 4(a), every pro-`p`-subgroup lies in a Sylow
  `p`-subgroup, p. 7).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §6, p. 68 (pro-`p`-groups), and Definition (1.6.8) and
  Theorem (1.6.9), p. 69 (Sylow subgroups of profinite groups).
