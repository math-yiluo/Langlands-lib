# The class formation of a local field

`Langlands/GaloisCohomology/Local/ClassFormation.lean`, namespace
`Langlands.GaloisCohomology.Local`.

For a nonarchimedean local field `K` with separable closure `Ksep`, the units `Ksepˣ` form a class
formation for `Gal(Ksep/K)` in the sense of `Langlands.ProfiniteCohomology.ClassFormation`
(Neukirch–Schmidt–Wingberg (3.1.8)): on every open subgroup `U` the invariant
`H²(U, Ksepˣ) ≃ ℚ/ℤ` is the invariant of the fixed field of `U`, `H¹(U, Ksepˣ) = 0` (Hilbert 90),
and restriction multiplies the invariant by the relative index.

## Declarations

- `classFormation K Ksep : ClassFormation (unitsModule K Ksep)`, built with
  `ClassFormation.ofAddEquiv` from `openInvariant K`, `isZero_cohomology_one_res_unitsModule` and
  `openInvariant_resOfLE`; `classFormation_invEquiv U`: its invariant on `U` is `openInvariant K U`.
- `res_top_comp_openCohomologyIso n`: restriction to the open subgroup `⊤` is restriction to its
  fixed field.
- `openInvariant_res_top x`, `classFormation_invEquiv_res_top x`: on `Gal(Ksep/K)` itself (the
  open subgroup `⊤`) the invariant of the class formation is `invariant K Ksep`.
- `subsingleton_cohomology_res_unitsModule_of_three_le U hr`: `Hʳ(U, Ksepˣ) = 0` for every open
  subgroup `U` and `r ≥ 3`; `subsingleton_cohomology_unitsModule_of_three_le hr`: the same for
  `Gal(Ksep/K)`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`:
`src/GroundTheory/ProfiniteCohomology/LocalClassFormationAlt.lean` (`localClassFormation`,
`localClassFormationOfIsSepClosure`, `localClassFormation_inv`: here `classFormation` and
`classFormation_invEquiv`) and the local half of
`src/GroundTheory/ProfiniteCohomology/ClassFormations/HighFormations.lean`
(`subsingleton_cohomology_galUnits_of_three_le`: here
`subsingleton_cohomology_unitsModule_of_three_le`) and of
`LocalClassFormation/FiniteVanishing/Vanishing.lean` (`subsingleton_cohomology_three_galUnits_open`).
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

The source's invariant (`brauerInv`, from its own local class field theory) is replaced by the
Library's `localBrauerInvariant` (see `Invariant.md`); the vanishing in degrees `≥ 3` is the
foundations' `ClassFormation.subsingleton_cohomology_of_three_le` (over `ULift ℤ`, any universe).
`res_top_comp_openCohomologyIso` and `openInvariant_res_top` are new.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter III, §1 (duality for
  class formations), pp. 147–163, and chapter VII, §1, Theorem (7.1.1) (the class field axiom for
  local fields), p. 371.
- J.-P. Serre, *Local Fields*, chapter XI (class formations), pp. 164–180, and chapter XIII, §4,
  Theorem 1 (the local class formation), p. 195.
