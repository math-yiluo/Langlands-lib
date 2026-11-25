# The local Tate pairing, and duality from a counting hypothesis

`Langlands/GaloisCohomology/Local/Duality/Pairing.lean`, namespace
`Langlands.GaloisCohomology.Local`.

For a nonarchimedean local field `K` with separable closure `Ksep` (`K Ksep : Type u`, any universe `u`) and a finite
smooth module `M` of `Gal(Ksep/K)` over `ℤ`, the local Tate pairing is
`Hʳ(M) × Hˢ(M') → H²(Ksepˣ) ≅ ℚ/ℤ` for `r + s = 2`, with `M' = Hom(M, Ksepˣ)` the Cartier dual. Its
perfectness is reduced, through the abstract duality theorem of the foundations (`DualizingData`,
with the dualizing module `μ_n`, `n = |M|`), to the perfectness of
`H¹(U, ℤ/n) × H¹(U, μ_n) → H²(U, μ_n) ≅ ℤ/n` on every open subgroup `U`. The left kernel of this
pairing vanishes by the norm index; if `|H¹(U, μ_n)| ≤ |H¹(U, ℤ/n)|`, counting gives perfectness.
That inequality is the hypothesis `CardCohomologyOneLe`; it is proved from the local Euler
characteristic formula in `Duality/Main.lean`, where the unconditional duality theorems are stated.

## Declarations

- `natCast_fixedField_ne_zero`: `n` stays invertible in every fixed field.
- `eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left hn U x h`: a class `x ∈ H¹(U, ℤ/n)` orthogonal
  to all of `H¹(U, μ_n)` is zero. (Every unit of the fixed field `E` of `U` is then a norm from the
  fixed field of the character, so the character is trivial by `eq_top_of_forall_exists_norm`.)
- `CardCohomologyOneLe K Ksep`: the statement `|H¹(U, μ_n)| ≤ |H¹(U, ℤ/n)|` for all open `U` and all
  `n` invertible in `K`.
- `isPerfectPairing_rootsOfUnityInvariant hn U hcard`: perfectness in degree one on `U`, given the
  inequality on `U`.
- `localDualizingData K Ksep hn hcard : DualizingData n μ_n` (finiteness and vanishing in degree `3`
  from `Dimension.lean`, `t_U = rootsOfUnityInvariant`), `localDualizingData_t`.
- `bijective_of_zmodToQZ`: transport of bijectivity of a pairing into `ℤ/n` to a pairing into
  `ℚ/ℤ`; `cohomologyAddEquivOfIso` (`cohomologyAddEquivOfIso_apply`): cohomology of isomorphic
  modules.
- `tatePairing K Ksep M h : Hʳ(M) →+ Hˢ(M') →+ ℚ/ℤ` (`tatePairing_apply`): cup product with values in
  `H²(Ksepˣ)` followed by `invariant K Ksep`.
- Instance `isSmoothRep_dualRep_rootsOfUnityModule`; `dualRepRootsOfUnityIso M n hM :
  Hom(M, μ_n) ≅ M'` for `M` killed by `n` (`dualRepRootsOfUnityIso_hom_apply`).
- `invariant_rootsOfUnityToUnits`, `tensorHom_dualRepRootsOfUnityIso_cartierPairing`,
  `tatePairing_coeffMap`: the Tate pairing is the abstract duality pairing for `μ_n` followed by
  `ℤ/n → ℚ/ℤ`.
- `finite_cohomology_cartierDual M hM r`: the cohomology of `M'` is finite.
- `tatePairing_bijective_of_card hcard M hM h`, `tatePairing_flip_bijective_of_card`: local Tate
  duality under the counting hypothesis.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/LocalTateDuality/EqZeroOfForallCupPairingZmodMulEqZeroLeft.lean`
(`natCast_fixedField_ne_zero`, `eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left`, the counting
in `isPerfectPairing_localInvRootsOfUnity`), `MainDefs.lean` (`localDualityHypotheses`: here
`localDualizingData`; `dualRepRootsOfUnityIso`; `localDualityPairing`: here `tatePairing`) and
`TensorHomDualRepRootsOfUnityIsoCartierPairing.lean` (`bijective_of_zmodToQZ`,
`cohomologyAddEquivOfIso`, `brauerInvOfIsSepClosure_rootsOfUnity`: here
`invariant_rootsOfUnityToUnits`, `tensorHom_dualRepRootsOfUnityIso_cartierPairing`,
`localDualityPairing_cohomologyMap`: here `tatePairing_coeffMap`,
`finite_cohomology_cartierDual_localField`: here `finite_cohomology_cartierDual`,
`bijective_localDualityPairing`, `bijective_localDualityPairing_flip`). The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`).

Changes: the pairing takes values in the Library's `RationalModIntegers` through `invariant K Ksep`
(the Library's invariant) in place of the source's `brauerInvOfIsSepClosure`. The source proves the
right kernel of the degree-one pairing trivial with the existence theorem and the reciprocity
isomorphism (`eq_zero_of_forall_cupPairing_zmodMul_eq_zero_right`, through
`exists_zmod_char_not_norm`); here the right kernel is controlled by counting, from the inequality
`CardCohomologyOneLe`, which is new (proved from the Euler characteristic in `Duality/Main.lean`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §2, Theorem
  (7.2.6) (Tate duality, stated for `p`-adic fields), p. 380.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.2, Theorems 1 and 2 (the dualizing module `μ` and
  local duality, for `p`-adic fields), p. 91.
