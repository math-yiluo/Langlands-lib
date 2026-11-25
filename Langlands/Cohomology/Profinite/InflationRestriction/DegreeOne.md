# Inflation and restriction in degree one

`Langlands/Cohomology/Profinite/InflationRestriction/DegreeOne.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a normal subgroup `N` of `G` and a smooth `A`: inflation `H¹(G/N, A^N) → H¹(G, A)` is
injective with image the kernel of restriction to `N`, and the image of restriction consists of
classes invariant under the conjugation action of `G` on `H¹(N, A)`.

## Declarations

- `conjHom S g : S →* S` (`s ↦ g⁻¹ s g` on a normal subgroup `S`), `coe_conjHom_apply`,
  `conjMor A S g` (the action of `g` on coefficients, compatible with `conjHom S g`),
  `conjMor_hom_apply`.
- `homologyπ_succ_eq_zero_iff`, `exists_iCycles_eq_of_d_eq_zero`, `homologyπ_surjective`,
  `iCycles_injective`: elementwise facts on cochain complexes indexed by `ℕ`.
- `toGroupCohomology_one_injective`: `H¹` of locally constant cochains injects into
  Mathlib's `H¹`.
- `invariantsIncl`, `infl_comp_res`: inflation followed by restriction is zero in positive degree.
- `infl_one_injective`: inflation in degree one is injective; `exists_infl_one_eq`: a class whose
  restriction to `N` vanishes is inflated.
- `cochains_d_zero_apply`, `cochains_d_one_apply`, `cochains_d_one_eq_zero_iff`,
  `cocycle_one_apply_one`: explicit differentials in degrees 0 and 1 (evaluation of cocycles).
- `continuous_conjHom`, `cohomologyConj A N n g` (conjugation by `g` on `Hⁿ(N, A)`),
  `cohomologyConjInvariants A N n` (the submodule of conjugation-invariant classes),
  `cocycleOneApply`, `cocycleOneApplyG` and their multiplicativity,
  `cohomologyConj_π_eq_iff`; `res_mem_cohomologyConjInvariants`: restricted classes are invariant.
- `card_ker_res_one (A) [IsSmoothRep A] (N : Subgroup G) [N.Normal] :
  Nat.card (LinearMap.ker (res A N 1).hom) = Nat.card (cohomology (A.quotientToInvariants N) 1)`:
  the classes vanishing on `N` are as many as `H¹(G/N, A^N)` (inflation is injective with image the
  kernel of restriction, `infl_one_injective`, `exists_infl_one_eq`);
  `invariantsQuotientEquiv A N : (A.quotientToInvariants N).ρ.invariants ≃ A.ρ.invariants`:
  `(A^N)^{G/N} = A^G`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/InflationRestriction/DegreeOne.lean` and
`InflationRestriction/CohomologyResMemCohomologyConjInvariants.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The source's
`GroundTheory.GroupCoh.conjHom`, `conjMor`, `coe_conjHom_apply`, `conjMor_hom_apply` (from its
`TateCohomology/ConjAction.lean`) are taken into this file: the Library's inner conjugation
(`Langlands.OrdinaryCohomology.innerConjugation`) acts on the whole group with the opposite
convention and does not apply to a normal subgroup. Other names are the source's.
`invariantsQuotientEquiv` is ported, from the same repository and commit, from
`src/GroundTheory/ArithmeticGeometry/SelmerPairing/Unramified.lean`; `card_ker_res_one` is not from
the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §6, Proposition (1.6.7), p. 67 (five term exact sequence; the
  image of restriction lies in `H¹(H, A)^{G/H}` by Proposition (1.6.3), p. 61).
- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.6 b), p. 15 (the exact sequence in low dimensions).
