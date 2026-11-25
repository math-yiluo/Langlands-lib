# The invariant on `H²(U, μ_n)` of a local field

`Langlands/GaloisCohomology/Local/Duality/RootsOfUnity.lean`, namespaces
`Langlands.ProfiniteCohomology` (corestriction, any topological group), `Langlands.GaloisCohomology`
and `Langlands.GaloisCohomology.Local`.

For a nonarchimedean local field `K`, a separable closure `Ksep`, `n` invertible in `K` and an open
subgroup `U` of `Gal(Ksep/K)`: the Kummer sequence identifies `H²(U, μ_n)` with the `n`-torsion of
`H²(U, Ksepˣ) ≅ ℚ/ℤ`, which gives `H²(U, μ_n) ≃ ℤ/n`, compatible with corestriction. These are the
data `t_U` of the abstract duality theorem (`DualizingData`) for the dualizing module `μ_n`.

## Declarations

- `coindMap_res_comp_coindTrace`, `cores_naturality`, `coresOfLE_naturality`,
  `coresOfLE_coeffMap`: corestriction (to the whole group, or between open subgroups `V ≤ U`) is
  natural in the coefficients.
- `nonempty_addEquiv_rootsOfUnityModule hn`: `μ_n(Ksep) ≅ ℤ/n` as groups, for `n` invertible in
  `K`; `nsmul_res_rootsOfUnityModule_eq_zero`: `μ_n` is killed by `n`.
- `kummerSequenceRes_g_hom_apply`: the last map of the restricted Kummer sequence is `x ↦ n • x`.
- `injective_coeffMap_kummerSequenceRes_f_two`: `H²(U, μ_n) → H²(U, Ksepˣ)` is injective (Hilbert
  90).
- `rootsOfUnityInv n U : H²(U, μ_n) → ℚ/ℤ` (image in `H²(U, Ksepˣ)` followed by the invariant of the
  class formation; `rootsOfUnityInv_apply`), injective (`rootsOfUnityInv_injective`) with image the
  `n`-torsion (`range_rootsOfUnityInv`).
- `rootsOfUnityInvariant hn U : H²(U, μ_n) ≃+ ℤ/n`, with `zmodToQZ_rootsOfUnityInvariant` (its image
  in `ℚ/ℤ` is `rootsOfUnityInv`) and `rootsOfUnityInvariant_coresOfLE` (compatibility with
  corestriction, from the corestriction law of the class formation).

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/LocalTateDuality/InjectiveCohomologyMapKummerSeqOpenFTwo.lean`
of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, with
`nsmul_res_galRootsOfUnity_eq_zero` from `LocalTateDuality/KummerCup.lean`. Renamed:
`cohomologyCores_naturality` → `cores_naturality`, `cohomologyCoresLE_naturality` →
`coresOfLE_naturality`, `cohomologyCoresLE_cohomologyMap` → `coresOfLE_coeffMap`,
`nonempty_addEquiv_galRootsOfUnity` → `nonempty_addEquiv_rootsOfUnityModule`,
`localInvRootsOfUnity` → `rootsOfUnityInvariant`, `localInvRootsOfUnity_cores` →
`rootsOfUnityInvariant_coresOfLE`; the source's `kummerSeqOpen` is `kummerSequenceRes` of
`Finiteness.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

The source's local class formation (on its own invariant) is replaced by `classFormation` (on the
Library's invariant); the source's `H¹` vanishing over open subgroups is the field layer's Hilbert
90. Stated for `K Ksep : Type u`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §2, Theorems
  (7.2.4) and (7.2.6), p. 380.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.2, Theorems 1 and 2 (the dualizing module `μ` and
  local duality, for `p`-adic fields), p. 91.
