# Ramified gamma stability for the two Hecke families

Supporting module of Task 5003 (module
`Langlands.Automorphic.AssociatedGammaRamifiedStability`). It derives the
`RamifiedGammaStability` input of the published two-twist engine for the automorphic and
arithmetic Hecke families. Henniart 2000, Théorème 2.3 uses twists that are highly ramified at
the other bad places, where the stable comparison of Henniart 1986, Lemma 4.2 applies.

## Results

- `exists_isCharacterTwist`: every class has a twist by every quasi-character (published
  `isCharacterTwist_iff_eq_twist`).
- `ramifiedGammaStability_families`: assume `StableTwistPairGammaMatchStatement` (proof Task
  6211), `CuspidalLocalGenericityStatement` (proved in the Library as
  `Automorphic.CuspidalPairPartialGamma.localGenericity`) and
  `ArithmeticPairEpsilonExistenceStatement` (proved in the Library as
  `Correspondence.arithmeticPairEpsilonExistence`). Assume also that the setups use
  the same additive components, that `T`, `T'` have central characters `ω`, `ω'` with
  `det S = ω ∘ τ_F` and `det S' = ω' ∘ τ_F`, and that `S`, `S'` have ranks `r + 1`, `t + 1`.
  Then for every finite set `T` there is a depth function with `RamifiedGammaStability`.

  Proof: at each place `z`, the stable comparison applies to the local classes of `P`, `P'`
  (generic by the genericity statement, with central characters `ω_z`, `ω'_z` by
  `centralActsBy_localClass`) and to `localPairClass S ι_z`, `localPairClass S' ι_z`
  (continuous of the right rank, with determinants `weilCharacter e ω_z`, `weilCharacter e ω'_z`
  by `determinantCharacter_localComponent`). This gives a bound `A_z`, and the depth is
  `A_z` (`choose`). A finite-order `χ` nontrivial on the principal units of depth `A_z` has
  local conductor `> A_z`, so the comparison gives `IsPairGammaMatch` for a twist of the
  local class of `P` by `χ_z` against the class twist of `localPairClass S ι_z`, which is the
  arithmetic class of the family (`localPairClass_twist_eq_twistClass`). The lemma
  `meromorphicEq_gamma_of_isPairGammaMatch` concludes.
