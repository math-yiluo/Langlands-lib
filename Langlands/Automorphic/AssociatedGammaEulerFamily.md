# Hecke Euler families with chosen partial L-functions

Supporting module for the proof of `AssociatedGammaStatement` (module `Langlands.Automorphic.AssociatedGammaEulerFamily`), glue step for the analytic input
`CommonTwistEulerInputs` of the published two-twist comparison engine
(`Langlands.Global.FunctionalEquationComparison`, module
`Langlands.Global.Factors.HeckeTwistComparisonStatement`). That engine only needs partial
L-functions to exist. So a `HeckeEulerFamily` is built from its local factors by choosing
partial L-functions whenever suitable ones exist.

## Declarations (namespace `…FunctionalEquationComparison.HeckeEulerFamily`)

- `HasEngineInputs l B`: for local factors `l` at all places and a finite set `B` of finite
  places, there are `σ` and partial L-functions `Lp`, `Lpd` such that the `FiniteEulerData`
  `⟨l, Lp, Lpd⟩` is `Admissible`, has Euler products outside `exceptionalPlaces K B` on
  `re s > σ`, and satisfies `FunctionalEquation` at `exceptionalPlaces K B`. As in
  `CommonTwistEulerInputs`, the decidable-equality instance comes from `classical`.
- `choosePartial l χ B`: the pair `(Lp, Lpd)` chosen from a witness of
  `HasEngineInputs (l χ) B` (classical choice), or `(0, 0)` if no witness exists.
- `ofLocalFactors l`: the `HeckeEulerFamily` with local factors `l` and partial L-functions
  `(choosePartial l χ B).1`, `(choosePartial l χ B).2`.
- `ofLocalFactors_spec`: if `HasEngineInputs (l χ) B`, then `(ofLocalFactors l).eulerData χ B`
  satisfies `Admissible`, `HasEulerProductsOutside … σ` (for some `σ`) and
  `FunctionalEquation` at `exceptionalPlaces K B`. Proof: the condition of `choosePartial`
  holds, so the Euler data are the chosen witnesses.
- `hasEulerProductsOutside_mono`: Euler products on `re s > σ` give Euler products on
  `re s > σ'` for `σ ≤ σ'`.
- `matchesOutside_exceptionalPlaces`: equality of the local L-factors and dual L-factors at
  every finite place outside `B`, on `re s > σ`, gives `MatchesOutside … (exceptionalPlaces K B) σ`.
  The infinite places all lie in `exceptionalPlaces K B = univ.disjSum B`.
- `commonTwistEulerInputs_ofLocalFactors`: suppose that for any two finite-order Hecke
  characters `χ₁`, `χ₂` with trivial infinity component there is a finite `B ⊇ T` such that
  both characters are unramified outside `B` and `HasEngineInputs` holds for both local
  factor families `lD`, `lE` and both characters at `B`. Suppose also that the finite local
  L-factors and dual L-factors of `lD` and `lE` agree outside `B` on a common right
  half-plane, for both characters. Then
  `CommonTwistEulerInputs K T (ofLocalFactors lD) (ofLocalFactors lE)`. Proof:
  `ofLocalFactors_spec` four times. The common half-planes are the maxima of the matching
  bound and the two Euler-product bounds for each character (`hasEulerProductsOutside_mono`).

## Overview of the supporting development for `AssociatedGammaStatement`

This module is the entry of a supporting development for
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup.AssociatedGammaStatement` (Henniart 2000,
Théorème 2.3). The development contains 25 modules in `Langlands/Automorphic/`. Together they
prove `associatedGamma_of_inputs` (module `Langlands.Automorphic.AssociatedGammaFinal`), which
derives the statement from two other statements:

- `Langlands.Global.CuspidalPairGlobalFunctionalEquationStatement` (the completed global
  Rankin–Selberg equation for cuspidal pairs);
- `Langlands.ClassFieldTheory.Global.RelativeWeilGroup.StableTwistPairGammaMatchStatement` (the stable
  local comparison under highly ramified twists).

The development therefore does not prove the statement. The second input is proved in the
Library (`stableTwistPairGammaMatchStatement`, module
`Langlands.Automorphic.StableTwistGammaMatchProof`); once the first is proved, the proof of the
statement applies `associatedGamma_of_inputs` to them.

The route follows Henniart's argument. Fix a finite place `v`. Build an automorphic and an
arithmetic Hecke Euler family, indexed by finite-order Hecke characters `χ` trivial at
infinity: the factors of `(Π ⊗ χ) × Π'` on one side and those of `((χ ∘ τ) ⊗ S) ⊗ S'` on the
other. Then verify the five inputs of the published two-twist engine
`Langlands.Global.FunctionalEquationComparison.heckeTwistComparison`. The engine gives equality
of the gamma factors at `v`. The modules, in dependency order:

- Engine glue: `AssociatedGammaEulerFamily` (this module: families from local factors),
  `AssociatedGammaCompletedEquation` and `AssociatedGammaCuspidalEquation` (a completed
  equation in the engine format), `AssociatedGammaLocalLink` (the gamma factor of a finite
  pair factor choice), `AssociatedGammaHeckeReduction` (the certificate
  `HasHeckeGammaCertificate` and `isPairGammaMatch_of_heckeGammaCertificate`).
- Arithmetic side: `AssociatedGammaArithmeticTwist` (local classes of twisted relative Weil
  representations), `AssociatedGammaArithmeticFamily` (the arithmetic family and its engine
  inputs from the proved `relativeWeilTwistFunctionalEquation`),
  `AssociatedGammaArithmeticGamma` (its local gamma factor).
- Automorphic side: `AssociatedGammaAutomorphicTwist` (local and archimedean effect of a
  Hecke determinant twist), `AssociatedGammaTwistedPairData` (local pair data of a twist),
  `AssociatedGammaAutomorphicFamily` (the automorphic family and its engine inputs from the
  global pair equation).
- Matching outside a finite set: `AssociatedGammaTensorEuler`, `AssociatedGammaUnramifiedMatch`,
  `AssociatedGammaOutsideMatch`, and `AssociatedGammaCommonInputs` (the input
  `CommonTwistEulerInputs`).
- Preservation at infinity and at `v`: `AssociatedGammaPreservation`.
- Local gamma matching: `AssociatedGammaLocalMatch`, `AssociatedGammaRamifiedInputs` and
  `AssociatedGammaRamifiedStability` (bad places, from the stable comparison),
  `AssociatedGammaPrincipalSeries`, `AssociatedGammaTriangular` and
  `AssociatedGammaOutsideStability` (good places, from the published principal-series
  comparison).
- Presentations: `AssociatedPresentationComparison` and
  `AssociatedPresentationSpectrum` (local classes and spherical spectra agree across
  presentations of one cuspidal realization; weak association transfers to any presentation).
- Assembly: `AssociatedGammaFinal`.

Each module's Markdown describes its results and proofs. The declarations are internal
deductions from Library definitions and theorems; no module formalizes a separate literature
theorem beyond the ones its Markdown names.
