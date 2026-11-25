# Cohomological dimension

`Langlands/Cohomology/Profinite/Dimension/Basic.lean`, namespace `Langlands.ProfiniteCohomology`.

For a prime `p` and a topological group `G`, the `p`-cohomological dimension `cd p G` is the
least `n ∈ {0, 1, …, ∞}` such that the `p`-primary part of `Hᵠ(G, A)` vanishes for all `q > n`
and all smooth torsion `G`-modules `A`; the strict `p`-cohomological dimension `scd p G` is the
same without the torsion hypothesis. `cdSup G` and `scdSup G` are their suprema over the primes.
For a profinite group, `cd p G ≤ n` can be tested on `p`-primary modules, or on simple modules
killed by `p` in degree `n + 1`, and `scd p G ≤ cd p G + 1`.

Coefficients are representations over `ULift ℤ` (the integers in the universe of `G`), smooth
in the sense of `IsSmoothRep`.

## Declarations

- `cd p G`, `scd p G`, `cdSup G`, `scdSup G` (definitions above, as infima in `ℕ∞` and suprema
  over `Nat.Primes`). `cd_le_iff`, `scd_le_iff`: the defining property;
  `primaryComponent_cohomology_eq_bot_of_cd_lt`: for a smooth torsion module `A` and `q > cd p G`,
  the `p`-primary component of `Hᵠ(G, A)` is zero; `scdSup_le_iff`.
- Additivity of coefficient maps: `cochainsMap_add`, `cohomologyMap_add`, `cohomologyMap_nsmul`,
  `cohomologyMap_nsmul_id_apply` (multiplication by `m` on `A` induces multiplication by `m` on
  cohomology); `nsmul_cohomology_eq_zero` (if `m` kills `A`, it kills `Hⁿ(G, A)`).
- `subsingleton_cohomology_of_subsingleton`; `subsingleton_cohomology_X₂`: if the cohomology of
  the outer terms of a short exact sequence vanishes in degree `n`, so does that of the middle
  term. `subQuotShortComplex A W h` (sub-representation, `A`, quotient), its exactness and
  smoothness, and `subsingleton_cohomology_of_sub_quot`.
- Primary components: `primaryComponent_eq_bot_iff`, `pow_nsmul_eq_zero_of_le`,
  `eq_zero_of_pow_nsmul_eq_zero`; `primaryComponent_cohomology_eq_bot_of_bijective` (if
  multiplication by `p` is bijective on `A`, the `p`-primary part of its cohomology vanishes);
  `primaryComponent_cohomology_eq_bot_iff_of_nsmul` (for `A` killed by `p`, the `p`-primary part
  vanishes iff the whole group does).
- `primarySubmodule A p`: the `p`-primary part of `A` (a `G`-stable submodule,
  `mem_primarySubmodule`, `primarySubmodule_le_comap`); `bijective_nsmul_quotient_primarySubmodule`:
  for a torsion `A`, multiplication by `p` is bijective on `A` modulo its `p`-primary part.
- `cd_le_of_forall_primary`, `subsingleton_cohomology_of_cd_le` (for `A` killed by `p`,
  `Hᵠ(G, A) = 0` for `q > cd p G`).
- Reduction to finite and to simple modules: `subsingleton_cohomology_of_finite_of_simple`
  (vanishing for simple modules killed by `p` gives vanishing for finite `p`-primary modules),
  `finite_sup_of_finite`, `exists_finite_stable_submodule` (for a compact group every element of
  a smooth `p`-primary module lies in a finite stable submodule),
  `subsingleton_cohomology_of_primary_of_finite` (vanishing for finite `p`-primary modules gives
  vanishing for all `p`-primary modules, by passage to the colimit), `primary_discreteCoind`,
  `primary_coindCokernel`, `subsingleton_cohomology_add_of_primary` (dimension shifting with
  coinduced modules: vanishing in degree `m + 1` for all `p`-primary modules gives vanishing in
  all higher degrees).
- `cd_le_iff_forall_primary`, `cd_le_iff_forall_simple`: for a compact group, `cd p G ≤ n` iff
  `Hᵠ(G, A) = 0` for all `q > n` and all `p`-primary smooth `A`, iff `H^{n+1}(G, A) = 0` for all
  simple smooth `A` killed by `p`.
- `cd_le_cdSup`, `scd_le_scdSup`, `scd_le_cd_add_one` (`scd p G ≤ cd p G + 1`),
  `scdSup_le_cdSup_add_one`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/CohomologicalDimension/PrimaryComponentCohomologyEqBotOfScdpLt.lean`
and `src/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Names: the source's `cdp p G`, `scdp p G`, `cd G`, `scd G` are here `cd p G`, `scd p G`,
`cdSup G`, `scdSup G`, and the lemma names follow: `cdp`/`scdp` → `cd`/`scd` and
`cd`/`scd` → `cdSup`/`scdSup` in every name (`cdp_le_iff` → `cd_le_iff`, `cdp_le_cd` →
`cd_le_cdSup`, `scdp_le_scd` → `scd_le_scdSup`, `subsingleton_cohomology_of_cdp_le` →
`subsingleton_cohomology_of_cd_le`, …).
The source's `IsDiscreteRep` is `IsSmoothRep`, its coefficient maps `cohomologyMap f n` are
`coeffMap f n` (the lemma names keep `cohomologyMap`).

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §3.1, p. 17 (definition of `cd_p`; Proposition 11: the
  criteria by `p`-primary modules and by simple modules killed by `p`), and §3.2, Proposition 13,
  p. 18 (`scd_p` equals `cd_p` or `cd_p + 1`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §3, Definition (3.3.1) and Proposition (3.3.2), p. 172, and
  Proposition (3.3.3), p. 173 (`cd_p G ≤ scd_p G ≤ cd_p G + 1`).

Both books define the cohomological dimensions for profinite groups; here `cd p G` and `scd p G` are
defined for every topological group.
