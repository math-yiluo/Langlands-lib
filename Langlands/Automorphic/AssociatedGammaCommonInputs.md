# The common-twist analytic input for the two Hecke families

Supporting module for the proof of `AssociatedGammaStatement` (module
`Langlands.Automorphic.AssociatedGammaCommonInputs`). It discharges the analytic input
`CommonTwistEulerInputs` of the published two-twist engine
(`HeckeTwistComparisonStatement`) for the automorphic family of an `AutomorphicTwistSetup`
and the arithmetic family of an `ArithmeticTwistSetup`, as needed for
`AssociatedGammaStatement` (Henniart 2000, Théorème 2.3: both sides satisfy global functional
equations with the same Euler factors outside a finite set). Internal deduction.

## Results

- `exists_finset_isUnramifiedMatchAt`: weak association `IsWeaklyAssociated S₀ s` gives a
  finite set `W ⊇ s.exceptional` outside which `S₀` is unramified and matches the Euler
  polynomial of `s` (published `isWeaklyAssociated_iff_exists_finset`).
- `commonTwistEulerInputs_families`: hypotheses are the completed global Rankin–Selberg
  equation `CuspidalPairGlobalFunctionalEquationStatement`, the
  existence statement `ArithmeticPairEpsilonExistenceStatement` (proved in the Library),
  nontriviality of `ψ` and triviality on `F`, weak association of `S`, `S'`, `S^∨`, `S'^∨` with
  the spectral systems of `P`, `P'`, `Pd`, `Pd'`, and the engine inputs of the arithmetic family
  for `B ⊇ T₀` (from `ArithmeticTwistSetup.exists_engineInputs`). Conclusion:
  `CommonTwistEulerInputs F T` for the two families built by `HeckeEulerFamily.ofLocalFactors`,
  for every finite `T`.

  Proof: for the two characters `χ₁`, `χ₂`, take the finite sets from the automorphic engine
  inputs (`AutomorphicTwistSetup.exists_engineInputs`), the ramification sets of `χ₁`, `χ₂`
  (`exists_finset_isUnramifiedAt`), the four weak-association sets, and all relevant
  exceptional sets of the original and twisted presentations; `B` is their union with `T` and
  `T₀`. Engine inputs hold at `B` for both families and both characters, and outside `B` the
  L-factors and dual L-factors agree at every `s` (`lFactor_eq_of_unramified`,
  `dualLFactor_eq_of_unramified`). The lemma `commonTwistEulerInputs_ofLocalFactors` concludes.
