# Reversal of cochains on cones (internal)

`Langlands/GaloisCohomology/CompactSupport/Internal/ConeReverse.lean`, namespace `Langlands.GaloisCohomology`. Internal: no stability promise.

The foundations' reversal of locally constant cochains (`revCochain`) is an endomorphism of the
cochain complex (`revLC`) acting as the identity in cohomology in degrees `0`, `1`, `2` through
explicit homotopies, natural in restriction, hence an endomorphism of the cochains with compact
support (`revCone`). It is used to compare the cup products with compact support in the left and in
the right factor with their signs, in the base case of the duality.

```lean
noncomputable def revLC : cochains A ⟶ cochains A
noncomputable def revCone : compactSupportCochains φ A Aᵥ a ⟶ compactSupportCochains φ A Aᵥ a
```

## Outline of the proofs

Reversal commutes with the differential (`d_revCochain` of the foundations) and with
restriction (`revLC_comp_cochainsMap`); in degrees `1` and `2` it differs from the identity by the
boundary of explicit cochains (`revHtpyOne`, `revHtpyTwo`), hence acts as the identity in cohomology
there. On the cocone, reversal on both components gives `revCone`, which is used to move the
compactly supported factor of a cup product from the left to the right with the sign `(−1)^{rs}`.

## Declarations

`LeibnizPairing.homologyMap_homology_eq_smul`, `continuous_revInv`, `isLocallyConstant_revCochain`, `revLinear`, `revLC`, `cochainOf_revLC`, `revCochain_zero`, `revLC_comp_cochainsMap`, `revD_zero_apply`, `revD_one_apply`, `revD_two_apply`, `revCochain_one_apply`, `revCochain_two_apply`, `revHtpyOne`, `revHtpyTwo`, `fin_one_eq_vec`, `fin_two_eq_vec`, `revCochain_one_sub`, `revCochain_two_sub`, `homologyMap_hom_apply_eq_self`, `d_iCycles_hom_apply`, `isLocallyConstant_revHtpyOne`, `continuous_vec_inv`, `isLocallyConstant_revHtpyTwo`, `cochainOf_sub'`, `revHtpyOneLC`, `revHtpyTwoLC`, `revHtpyTwo_zero`, `revLC_one_sub`, `revLC_two_sub`, `revHtpyTwoLC_zero`, `homologyMap_revLC_one`, `homologyMap_revLC_two`, `cochainsMap_revHtpyTwoLC`, `localRes_comp_piMap_revLC`, `revCone`, `homologyMap_piMap_revLC_two`, `homologyMap_revCone_localToCompact`, `coconeMkSucc`, `coconeMkZero`, `coconeFst`, `coconeSndSucc`, `coconeMkSucc_smul`, `coconeMkSucc_eq_iff`, `d_coconeMkSucc`, `d_coconeMkZero`, `coconeLeft_μ_coconeMkSucc`, `coconeRight_μ_coconeMkSucc`, `compactMkSucc`, `compactMkZero`, `compactMkSucc_sub`, `compactMkSucc_eq_iff`, `d_compactMkSucc`, `d_compactMkZero`, `revCone_f_compactMkSucc`, `cochainOf_localRes_one_apply`, `cochainOf_d_zero_one_apply`, `revCone_one_sub`, `piRevHtpyOne`, `compactMkSucc_zero`, `cocycle_components`, `homologyMap_revCone_one`, `revCone_two_sub`, `homologyMap_revCone_two`, `homologyMap_revCone_three`, `resPairingAlong`, `revCochain_hom`, `revLC_cupPairingCochains`, `braiding_comp_resPairingAlong`, `compactCupRightRes`, `compactCupLeibnizRes`, `compactCupRightLeibnizRes`, `compactMkSucc_smul`, `neg_one_pow_succ_mul_mul`, `revCone_compactCup_succ`, `revCone_compactCup_zero`, `revCone_compactCupLeibnizRes`, `compactCupRes_eq_neg_one_pow_smul_compactCupRightRes`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseReverse.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. The source's reversal of cochains is the foundations' `revCochain` (`Langlands/Cohomology/Profinite/Cup/Graded.lean`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter I, §4, Propositions (1.4.1), p. 36, and (1.4.3), pp. 38–39 (cup products of cochains and their compatibility with connecting maps). (Proposition (1.4.4), p. 39, for the graded commutativity of the cup product.)
