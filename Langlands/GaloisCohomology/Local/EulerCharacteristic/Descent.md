# Conjugation on cohomology and coprime descent

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Descent.lean`, namespace `Langlands.ProfiniteCohomology`.

For a normal subgroup `N` of a profinite group `G`, conjugation by `g ∈ G` acts on `Hⁿ(N, A)`
(`cohomologyConj`), trivially for `g ∈ N`, giving a representation of `G/N`. The restriction map
lands in the invariants of this action, and for an open normal subgroup `U` of index invertible on
`A` (`[G:U]` acts bijectively on `A`), restriction is an isomorphism
`Hⁿ(G, A) ≅ Hⁿ(U, A)^{G/U}` (`coprimeDescentEquiv`), by the corestriction identity
`cores ∘ res = [G:U]`.

## Declarations

- `cohomologyConj_one`, `cohomologyConj_mul`, `cohomologyConj_naturality`, `conjShortComplexMor`,
  `δ_comp_cohomologyConj`, `cohomologyConj_of_mem`, `cohomologyConj_eq_of_mk_eq`.
- `cohomologyConjRep A N n : Representation k (G ⧸ N) (Hⁿ(N, A))`, `cohomologyConjRep_mk`,
  `mem_cohomologyConjInvariants_iff`.
- `cohomologyRes_comp_cohomologyConj`, `cohomologyRes_apply_mem_cohomologyConjInvariants`.
- `bijective_nsmul_cohomology`, the coinduction trace (`coindTraceTermMor`,
  `cohomologyCores_comp_cohomologyRes`, `cohomologyRes_cohomologyCores_apply`),
  `cohomologyRes_injective_of_bijective`, `range_cohomologyRes_of_bijective`.
- `coprimeDescentEquiv U A hA n : Hⁿ(G, A) ≃ Hⁿ(U, A)^{G/U}`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ConjAction.lean` and `Descent.lean`. Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The conjugation map
`cohomologyConj` itself is the foundations' (`Langlands.Cohomology.Profinite.InnerConjugation`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter I, §5, Proposition
  (1.5.4) (conjugation commutes with inflation, restriction and corestriction), p. 50, and §6,
  Proposition (1.6.1), p. 60.
- J.-P. Serre, *Galois Cohomology*, chapter I, §2.4, Proposition 9 (`Cor ∘ Res = n`), p. 12.
