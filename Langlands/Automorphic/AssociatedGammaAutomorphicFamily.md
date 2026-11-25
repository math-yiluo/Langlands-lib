# The automorphic Hecke Euler family of a cuspidal pair

Supporting module for the proof of `AssociatedGammaStatement` (module
`Langlands.Automorphic.AssociatedGammaAutomorphicFamily`, namespace
`Langlands.Global.CuspidalPairFunctionalEquation`). It builds the automorphic side `D` of the
two-twist comparison engine used for `AssociatedGammaStatement` (Henniart 2000, Théorème
2.3, which applies the global Rankin–Selberg functional equation to `(Π ⊗ χ) × Π'` for
characters `χ` with prescribed local behaviour). It derives the engine's analytic input from
the completed global equation `CuspidalPairGlobalFunctionalEquationStatement`. That
statement is a hypothesis here.

## Data

`AutomorphicTwistSetup ψ r t` bundles cuspidal realizations `T`, `T'`, contragredients
`Td`, `Td'`, presentations `P`, `P'`, `Pd`, `Pd'` with irreducible admissible components,
finite additive components of `ψ` with self-dual measures, archimedean additive components,
archimedean standard-module parameters of all four realizations, and one infinite place
`w₀`.

## Local factors

`localFactors χ` is

- at infinite places: the published `lumpedArch w₀` of the archimedean L-factor of the pair,
  that of the contragredient pair, and the archimedean epsilon factor (the shapes in
  `CuspidalPairGlobalFunctionalEquationStatement`), independent of `χ`
  (`localFactors_inl`);
- at a finite place `z`: `pairDataFactors` of `twistedPairData` for
  `(π_z, π'_z)` twisted by `quasicharacterBase z (χ.finiteComponent z)` (module `Langlands.Automorphic.AssociatedGammaTwistedPairData`). It depends on `χ` only through `χ_z`
  (`localFactors_inr_of_finiteComponent_eq`).

## Results

- `isSmoothDual_localClass`: local classes of presentations of a contragredient pair are
  smooth duals (published `cuspidalContragredientLocalCompatibility`).
- `HeckeCharacter.hasPrescribedInfinityComponent_one_inv`: triviality at infinity passes to
  `χ⁻¹`.
- `finiteData_specs`: the twisted data at `z` are the L-polynomials and epsilon factor of the
  local classes of the twisted presentations `P ⊗ χ`, `Pd ⊗ χ⁻¹` and of `P'`, `Pd'`. Proof:
  the local class of `P ⊗ χ` is the `χ_z`-twist of that of `P` (module
  `Langlands.Automorphic.AssociatedGammaAutomorphicTwist`, (A)); `Td ⊗ χ⁻¹` is a contragredient of `T ⊗ χ` ((C)),
  so the local classes are smooth duals; uniqueness of twists and duals
  (`IsTwistedPairData.specs`).
- `twistedChoice χ`: the resulting `FinitePairFactorChoice` of the twisted quadruple.
- `exists_engineInputs` (main): assume the completed global equation, `ψ` nontrivial and
  trivial on `F`. For every `χ` trivial at infinity there is a finite `S` with
  `twistedChoice χ` unramified outside `S` and `HasEngineInputs (localFactors χ) B` for every
  `B ⊇ S`. Proof: apply the global equation to `(T ⊗ χ, Td ⊗ χ⁻¹, T', Td')` with the twisted
  presentations; the archimedean parameters of `T`, `Td` serve for the twists ((B), using
  that `χ` and `χ⁻¹` are trivial at infinity); feed `twistedChoice χ` to the lemma
  `FinitePairFactorChoice.exists_engineInputs_cuspidal`, whose Euler data are by definition
  `localFactors χ`.
