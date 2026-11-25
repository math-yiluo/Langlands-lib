# Open normal subgroups of a topological group

`Langlands/Cohomology/Profinite/OpenNormal.lean`, namespace `Langlands.ProfiniteCohomology`.

Facts on open normal subgroups used throughout the cohomology of profinite groups.

## Declarations

- `OpenNormalSubgroup.instNonempty`: a topological group has an open normal subgroup (itself).
- `OpenNormalSubgroup.mem_nhds_one`: an open normal subgroup is a neighbourhood of `1`.
- `OpenNormalSubgroup.discreteTopology_quotient`, `OpenNormalSubgroup.finite_quotient`: the
  quotient by an open normal subgroup is discrete, and finite if the group is compact.
- `OpenNormalSubgroup.hasBasis_nhds_one`: in a compact totally disconnected group (a profinite
  group) the open normal subgroups form a basis of neighbourhoods of `1`;
  `OpenNormalSubgroup.hasBasis_nhds_one_pi`: the sets `U^ι` do so in `G^ι` for finite `ι`.
- `exists_openNormalSubgroup_pi_of_isLocallyConstant`: a locally constant function on `G^ι`
  (`ι` finite, `G` profinite) is constant on the classes modulo `U^ι` for some open normal `U`;
  `exists_openNormalSubgroup_factor_of_isLocallyConstant`: it factors through `(G/U)^ι`; the
  `…_fin_…` forms are the cases `ι = Fin n` used for cochains.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/OpenNormal.lean` and
`src/GroundTheory/ProfiniteCohomology/Factor.lean` of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The source declarations
`GroundTheory.ProfCoh.OpenNormalSubgroup.*` and `GroundTheory.ProfCoh.exists_openNormalSubgroup_*`
keep their names under `Langlands.ProfiniteCohomology`; the statements and proofs are unchanged.

## References

- J.-P. Serre, *Cohomologie galoisienne*, chapter I, §1.1 (profinite groups), in the English
  translation *Galois Cohomology* (Springer, 1997; corrected second printing 2002), p. 3:
  Proposition 0 and its proof (in a compact totally disconnected group the open normal subgroups
  form a base of neighbourhoods of `1`, and an open subgroup has finite index).
