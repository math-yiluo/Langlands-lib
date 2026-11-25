# Groups of order two and duality of involutions

`Langlands/GaloisCohomology/CompactSupport/TateModified/OrderTwo.lean`, namespace `Langlands.GaloisCohomology`.

For a group `{1, c}` of order two acting discretely on `A`: `H¹(G, A) ≅ ker(1 + c)/im(1 − c)`,
`H²(G, A) ≅ A^G / im(1 + c)` and `Ĥ⁰(G, A) ≅ A^G / im(1 + c)` (`h1EquivOfOrderTwo`,
`h2EquivOfOrderTwo`, `cohomZeroEquivContinuous`), by explicit cocycles. For a finite abelian group
with an involution `σ`, the groups `ker(σ − 1)/im(1 + σ)` of `σ` and of the dual involution are in
perfect duality (`tatePair_bijective`). These describe the local terms at the real places.

```lean
def h1EquivOfOrderTwo : tateQuot (-act A c) ≃+ cohomology A 1
def h2EquivOfOrderTwo : tateQuot (act A c) ≃+ cohomology A 2
def cohomZeroEquivContinuous : tateQuot (act A c) ≃+ cohomologyTateZero A
def tatePair (σ : M →+ M) : tateQuot σ →+ tateQuot (dualInv σ) →+ QZ
theorem tatePair_bijective [Finite M] : Function.Bijective (tatePair σ)
theorem tatePair_flip_bijective [Finite M] : Function.Bijective (tatePair σ).flip
```

## Outline of the proofs

For `G = {1, c}` discrete, a `1`-cocycle is determined by its value `α` at `c`, with
`α + cα = 0`, and is a coboundary exactly when `α ∈ im(1 − c)`; a `2`-cocycle is cohomologous to one
supported at `(c, c)` with invariant value, a coboundary exactly when the value is a trace. For an
involution `σ` of a finite abelian group, the pairing of `ker(σ − 1)/im(1 + σ)` with the same group
for the dual involution is perfect by counting with Pontryagin duality.

## Declarations

`mul_self_eq_one`, `inv_eq_self`, `d_zero_apply`, `d_one_apply`, `d_two_apply`, `cochainOf_d_zero`, `cochainOf_d_one`, `cochainOf_d_two`, `cochainOf_sub`, `cocycle_one`, `cocycle_two`, `cohomologyπ_one_eq_zero_iff`, `cohomologyπ_two_eq_zero_iff`, `cochainOne`, `cochainOne_one`, `cochainOne_c`, `d_cochainOne`, `cocycleOne`, `cochainOf_cocycleOne`, `exists_eq_cocycleOne`, `cohomologyπ_cocycleOne_eq_zero_iff`, `cochainTwo`, `cochainTwo_cc`, `cochainTwo_one_left`, `cochainTwo_one_right`, `d_cochainTwo`, `cocycleTwo`, `cochainOf_cocycleTwo`, `cohomologyπ_cocycleTwo_eq_zero_iff`, `exists_eq_cocycleTwo_of_normalized`, `exists_cohomologyπ_eq_cocycleTwo`, `norm_apply`, `fixedSub`, `mem_fixedSub`, `traceSub`, `mem_traceSub`, `traceSub_le_fixedSub`, `tateQuot`, `dualInv`, `dualInv_apply`, `mem_fixedSub_dualInv_iff`, `fixedPair`, `fixedPair_apply`, `two_nsmul_fixedPair`, `fixedPair_eq_zero_of_mem_left`, `fixedPair_eq_zero_of_mem_right`, `tatePair`, `tatePair_mk`, `tatePair_injective`, `tatePair_flip_injective`, `finite_tateQuot`, `tatePair_bijective`, `tatePair_flip_bijective`, `fixedSubCongr`, `coe_fixedSubCongr_apply`, `tateQuotCongr`, `tateQuotCongr_mk`, `act`, `mem_fixedSub_neg_act`, `mem_fixedSub_act`, `cocycleOne_add`, `cocycleTwo_add`, `h1Hom`, `h1Hom_apply`, `h1EquivOfOrderTwo`, `h1Equiv_mk`, `h2Hom`, `h2Hom_apply`, `h2EquivOfOrderTwo`, `h2Equiv_mk`, `mem_invariants_of_fixed`, `h0HomOfOrderTwo`, `h0Hom_apply`, `H0Iso_inv_injective`, `cohomZeroEquivContinuous`, `h0Equiv_mk`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/OrderTwo.lean`, `RealPlaces/InvolutionDuality.lean` and `RealPlaces/OrderTwoTate.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. Bare `cocycles` is qualified as `ProfiniteCohomology.cocycles` (both it and Mathlib's `groupCohomology.cocycles` are open here).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter I, §7, Proposition (1.7.1), p. 74 (`Ĥ^{2n}(G, A) ≅ A^G/N_G A` and `Ĥ^{2n−1}(G, A) ≅ N_G A/I_G A` for cyclic `G`).
