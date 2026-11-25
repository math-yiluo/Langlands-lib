# Shapiro's lemma for open subgroups

`Langlands/Cohomology/Profinite/Shapiro.lean`, namespace `Langlands.ProfiniteCohomology`.

For a compact group `G`, an open subgroup `U` and a smooth representation `B` of `U`, Mathlib's
coinduced representation `Rep.coind U.subtype B` is smooth, and restriction to `U` followed by
evaluation at `1` is an isomorphism `Hⁿ(G, Coind_U^G B) ≅ Hⁿ(U, B)` (Shapiro's lemma).

## Declarations

- `coindEvalOne U B`: evaluation at `1`, a morphism `Rep.res U.subtype (Rep.coind U.subtype B) ⟶ B`;
  `coindUnit U A : A ⟶ Rep.coind U.subtype (Rep.res U.subtype A)` (the unit of the adjunction),
  with `coindUnit_comp_coindEvalOne`.
- `isLocallyConstant_coind`, `coindToLocallyConstant`, `isSmoothRep_coind`: the coinduced
  representation of a smooth `B` is smooth; `finiteIndex_openSubgroup`,
  `compactSpace_openSubgroup`: an open subgroup of a compact group has finite index and is
  compact.
- `shapiroMap U B n`: the map `map (subgroupInclusion U) (coindEvalOne U B) n`.
- `coindShortComplexOf`, `shortExact_coindShortComplexOf`, `coindEvalOneShortComplex`:
  coinduction is exact and compatible with evaluation; `shapiroMap_naturality`.
- `coindDiscreteCoindIso`, `isZero_cohomology_coind_discreteCoind`: coinducing a coinduced
  module gives a coinduced module, hence an acyclic one.
- `coind_invariant_apply`, `coindInvariantsEval`, `coindInvariantsEval_bijective`,
  `isIso_shapiroMap_zero`: the case `n = 0`.
- `isIso_shapiroMap` (by dimension shifting), and `shapiroIso U B n :
  cohomology (Rep.coind U.subtype B) n ≅ cohomology B n`, with `shapiroIso_hom`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ShapiroDefs.lean` (except its section on the
trace) and `src/GroundTheory/ProfiniteCohomology/Shapiro.lean` (except its section on
corestriction) of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's; `shapiroMap` is built with the single `map` and
`subgroupInclusion` in place of `cohomologyMapAlong … (continuous_subgroup_subtype _)`.
`shapiroMap_naturality` is proved with `backward.isDefEq.respectTransparency false` (coefficient
maps used at the type `Rep.res (.id _) B ⟶ B'`).

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.5, Proposition 10, p. 13 (`H^q(G, M_G^H(A)) ≅ H^q(H, A)`
  for a closed subgroup `H`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §6, Proposition (1.6.4), p. 62 (Shapiro's lemma for a closed
  subgroup `H` and `Ind_G^H(A)`).

Both books state the lemma for closed subgroups of a profinite group; here `U` is an open subgroup
of a compact group.
