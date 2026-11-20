# Henniart's Théorème 2.3 over totally complex fields from the totally complex functional equation

Module `Langlands.Automorphic.AssociatedGammaTCReductionProof`. Author: Worker 1011. Proof
contribution to Task 7361 (`0610fbb5-7b81-4ff7-b8bf-24d14a7a0c2d`), revision 1, link 2 of the
totally complex chain that Task 0 published under the operator's answer
`81ed24709e7050068786116ca6613260` (Option A).

## 1. What is proved

The theorem
`Langlands.ClassField.Global.RelativeWeilGroup.associatedGammaReductionTC.{u, uV, uP, uQ, uE}`
proves the published proposition

```text
AssociatedGammaReductionTCStatement.{u, uV, uP, uQ, uE} :=
  Langlands.Global.CuspidalPairGlobalFunctionalEquationTCStatement.{u, u} →
    AssociatedGammaTCStatement.{u, uV, uP, uQ, uE}
```

of module `Langlands.Automorphic.AssociatedFactorTCReductionStatement`
([`AssociatedFactorTCReductionStatement`](AssociatedFactorTCReductionStatement.md)), at five
arbitrary independent universe levels and with no further hypothesis.

- The premise, from module `Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement`,
  is the completed global Rankin–Selberg functional equation of cuspidal pairs over every
  totally complex number field.
- The conclusion, from module `Langlands.Automorphic.AssociatedFactorTCStatement`
  ([`AssociatedFactorTCStatement`](AssociatedFactorTCStatement.md)), is Henniart (2000),
  Théorème 2.3, for every totally complex number field `F` and every finite Galois extension
  `E/F`. For the gamma factors at a finite place `v` of `F`, it asserts `IsPairGammaMatch`
  between the local classes of two cuspidal realizations and the local pair classes of two
  weakly associated representations of the relative Weil group `W_{E/F}`.

The theorem is not a proof of the totally complex Théorème 2.3 itself: its premise,
`CuspidalPairGlobalFunctionalEquationTCStatement`, is an open statement of the Library.

## 2. Route

The published theorem `associatedGamma_of_inputs` (module
`Langlands.Automorphic.AssociatedGammaFinal`, [`AssociatedGammaFinal`](AssociatedGammaFinal.md))
derives the unrestricted `AssociatedGammaStatement` from the unrestricted
`CuspidalPairGlobalFunctionalEquationStatement.{u, u}` and
`StableTwistPairGammaMatchStatement.{u, uV, uE}`. Its proof applies the functional equation
only at the base field `F` of the conclusion. Three published auxiliary results pass the
functional equation through, each with the unrestricted statement as a hypothesis:

| Published result | Module |
|---|---|
| `AutomorphicTwistSetup.exists_engineInputs` | `Langlands.Automorphic.AssociatedGammaAutomorphicFamily` |
| `commonTwistEulerInputs_families` | `Langlands.Automorphic.AssociatedGammaCommonInputs` |
| `hasHeckeGammaCertificate_setups` | `Langlands.Automorphic.AssociatedGammaFinal` |

The unrestricted functional equation is not available from the totally complex one, so
these results cannot be applied as they are. This module therefore contains totally complex
copies of the three results and of `associatedGamma_of_inputs`. Each copy differs from its
original in two ways only:

1. the hypothesis `hFE : CuspidalPairGlobalFunctionalEquationTCStatement` replaces
   `hFE : CuspidalPairGlobalFunctionalEquationStatement`, at the same universe levels;
2. the instance `[NumberField.IsTotallyComplex F]` is added after `[NumberField F]` for the
   field at which `hFE` is applied (in `associatedGamma_of_inputs_tc`, it is introduced from
   the conclusion `AssociatedGammaTCStatement`).

The proof terms are otherwise verbatim copies of the originals; only the names of the copied
results they call change. Every application `hFE F ψ …` now finds the instance
`NumberField.IsTotallyComplex F` in context. The totally complex premise has the same
conclusion as the unrestricted one. Its real-place clauses quantify over
`{v : InfinitePlace F // v.IsReal}`, which is empty for a totally complex field. The proof
does not use this emptiness: it extracts the real-place choices with `choose` exactly as the
original does.

## 3. The declarations

### 3.1 `AutomorphicTwistSetup.exists_engineInputs_tc`

Namespace `Langlands.Global.CuspidalPairFunctionalEquation.AutomorphicTwistSetup`, universes
`u uQ`. The totally complex form of `exists_engineInputs`. Hypotheses: a totally complex
number field `F` with compact adele quotient, an `AutomorphicTwistSetup.{u, uQ} ψ r t` `D`,
the totally complex functional equation at `{u, uQ}`, `ψ` nontrivial and trivial on `F`, and
a Hecke character `χ` trivial at infinity. Conclusion: a finite set `S` of finite places
such that `D.twistedChoice χ` is unramified outside `S` and
`HeckeEulerFamily.HasEngineInputs (D.localFactors χ) B` holds for every `B ⊇ S`.

Proof (as in the original):

1. `χ⁻¹` is trivial at infinity (`HeckeCharacter.hasPrescribedInfinityComponent_one_inv`), and
   `Td ⊗ χ⁻¹` is a contragredient of `T ⊗ χ`
   (`OperatorRealization.IsContragredientOf.heckeDeterminantTwist_inv`).
2. Apply `hFE` at `F` to `(T ⊗ χ, Td ⊗ χ⁻¹, T', Td')` with the twisted presentations
   (`heckeDeterminantTwist_hasIrreducibleAdmissibleComponents`). This gives `S`.
3. Specialize its last clause to the finite choice `D.twistedChoice χ` and to the archimedean
   data of `D`. The parameters of `T`, `Td` serve for the twists
   (`OperatorRealization.HasRealPlaceParameter.heckeDeterminantTwist`,
   `OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist`).
4. `FinitePairFactorChoice.exists_engineInputs_cuspidal` turns the completed equation into
   the engine inputs.

### 3.2 `commonTwistEulerInputs_families_tc`

Namespace `Langlands.ClassField.Global.RelativeWeilGroup`, universes `u uQ uV uE`. The totally
complex form of `commonTwistEulerInputs_families`. Hypotheses: a totally complex `F`, a finite
Galois extension `E/F`, the totally complex functional equation, the epsilon existence
statement `Correspondence.ArithmeticPairEpsilonExistenceStatement`, setups `D` and `A`, weak
association of `S`, `S'`, `S^∨`, `S'^∨` with the spectral systems of `D.P`, `D.P'`, `D.Pd`,
`D.Pd'`, and the engine inputs of the arithmetic family for `B ⊇ T₀`. Conclusion:
`CommonTwistEulerInputs F T` for the automorphic and arithmetic families, for every finite
`T`.

Proof (as in the original): for two characters `χ₁`, `χ₂`, collect these finite sets:

- those of `exists_engineInputs_tc` (§3.1);
- the ramification sets of `χ₁`, `χ₂` (`HeckeFunctionalEquation.exists_finset_isUnramifiedAt`);
- the four weak-association sets (`exists_finset_isUnramifiedMatchAt`);
- the exceptional sets of the original and twisted presentations.

Take `B` to be their union with `T` and `T₀`. Engine inputs hold at `B` for both families and
both characters. Outside `B` the L-factors and dual L-factors agree
(`lFactor_eq_of_unramified`, `dualLFactor_eq_of_unramified`), and
`HeckeEulerFamily.commonTwistEulerInputs_ofLocalFactors` concludes.

### 3.3 `hasHeckeGammaCertificate_setups_tc`

Namespace `Langlands.ClassField.Global.RelativeWeilGroup`, universes `u uQ uV uE`. The totally
complex form of `hasHeckeGammaCertificate_setups`. It has the hypotheses of the original:

- the stable comparison `StableTwistPairGammaMatchStatement`, the principal-series
  comparison `PrincipalSeriesPairGammaMatchStatement`, the epsilon existence statement and
  local genericity `Automorphic.CuspidalLocalGenericityStatement`;
- `IsArithmeticClassFamily c`;
- the setups `D`, `A` with equal finite additive components;
- the four weak associations;
- central characters `ω`, `ω'` with `det S = ω ∘ τ` and `det S' = ω' ∘ τ`.

In addition, it has the instance `[NumberField.IsTotallyComplex F]`, and the totally complex
functional equation replaces the unrestricted one. Conclusion: `HasHeckeGammaCertificate` at
every finite place `v` for the data of the setups at `v`.

Proof (as in the original): the bad set is `{v} ∪ W₁ ∪ W₂`.

1. The engine inputs come from:
   - `ArithmeticTwistSetup.exists_engineInputs` (arithmetic family);
   - `commonTwistEulerInputs_families_tc` (§3.2, the only use of `hFE`);
   - `infinityGammaPreservation_families` and `finiteGammaPreservation_families`;
   - `ramifiedGammaStability_families` (stable comparison);
   - `outsideGammaStability_families` (principal-series comparison).
2. The gamma factors at `v` are those of the untwisted families. On the automorphic side they
   come from `Correspondence.twistedPairData_spec` and `IsTwistedPairData.exists_gamma`, using
   `HeckeCharacter.finiteComponent_one`, `quasicharacterBase_one`,
   `Correspondence.isCharacterTwist_one` and `Correspondence.IsCharacterTwist.unique`. On the arithmetic side
   they come from `ArithmeticTwistSetup.finiteFactors_spec`,
   `IsArithmeticPairLocalFactors.exists_gamma` and `localPairClass_dual`, using
   `localPairClass_twist_of_trivial` and `reciprocityCharacter_one_apply`.
3. The rational continuation of the automorphic gamma factor is
   `hasRationalContinuation_pairDataFactors_gamma`.

### 3.4 `associatedGamma_of_inputs_tc`

Namespace `Langlands.ClassField.Global.RelativeWeilGroup`, universes `u uV uP uQ uE`.
Hypotheses `hFE : CuspidalPairGlobalFunctionalEquationTCStatement.{u, u}` and
`hL1 : StableTwistPairGammaMatchStatement.{u, uV, uE}`. Conclusion:
`AssociatedGammaTCStatement.{u, uV, uP, uQ, uE}`. The proof is that of
`associatedGamma_of_inputs`. The only change is one more introduced instance, the
`NumberField.IsTotallyComplex F` of the conclusion, and the call of
`hasHeckeGammaCertificate_setups_tc` in place of the original:

1. Replace `P`, `P'` by presentations `Q`, `Q'` at `{u, u}` whose local components are
   irreducible and admissible at every place
   (`Automorphic.cuspidalAllLocalIrreduciblePresentationExistence`). Choose contragredients
   `Td`, `Td'` (`Automorphic.cuspidalContragredientExistence`) and presentations `Qd`, `Qd'` of
   them with the same property (`Automorphic.cuspidalDualPresentationExistence`, then the
   first result again). The local classes at `v` are unchanged
   (`Automorphic.CuspidalSpectralPresentation.localComponent_padicClass_eq`).
2. Weak association passes to `Q`, `Q'` (`IsWeaklyAssociatedClass.presentation`) and to the
   duals (`presentedContragredientAssociation`). Central characters `ω`, `ω'` with
   `det S = ω ∘ τ` come from `associatedCentralCharacter`.
3. `ψ` is nontrivial because its finite component `ψ_v` is. Applied at `F` to
   `(T, Td, T', Td')`, `Q`, `Q'`, `Qd`, `Qd'`, the totally complex functional equation gives a
   finite factor choice (finite additive components and self-dual measures) and the
   archimedean additive components and parameters; `choose` makes them functions.
4. By `isPairGammaMatch_of_heckeGammaCertificate` it suffices to give a gamma certificate for
   every self-dual measure `ν` of `ψ_v`. Build the setups `D` and `A`, replacing at `v`
   (with `Function.update`) the measure by `ν`, the local-map data by the given `(w, e, ι)` and
   the local-constant system by the given `(eC, ε)`. Away from `v` the data come from
   `exists_localWeilData` and `exists_localSystem`. The finite component at `v` is `ψ_v`
   (`isCanonicalFiniteAdditiveComponent_unique`).
5. Apply `hasHeckeGammaCertificate_setups_tc`, with the proved inputs
   `principalSeriesPairGammaMatchStatement`, `Correspondence.arithmeticPairEpsilonExistence`
   and `Automorphic.CuspidalPairPartialGamma.localGenericity`. Then rewrite the setup data at
   `v` to the given data.

### 3.5 `associatedGammaReductionTC`

Namespace `Langlands.ClassField.Global.RelativeWeilGroup`, universes `u uV uP uQ uE`, type
`AssociatedGammaReductionTCStatement.{u, uV, uP, uQ, uE}`. Proof: given `hFE`, apply
`associatedGamma_of_inputs_tc` (§3.4) to `hFE` and to the Library theorem
`stableTwistPairGammaMatchStatement.{u, uV, uE}`, which proves the stable comparison
(module `Langlands.Automorphic.StableTwistGammaMatchProof`).

## 4. Imported results

The module imports `Langlands.Automorphic.AssociatedFactorTCReductionStatement` (the target and,
through it, the two totally complex statements), `Langlands.Automorphic.AssociatedGammaFinal`
(which imports every module of the original route) and
`Langlands.Automorphic.StableTwistGammaMatchProof`. The results used are all published and
proved:

| Result | Module |
|---|---|
| `HeckeCharacter.hasPrescribedInfinityComponent_one_inv`, `AutomorphicTwistSetup.twistedChoice`, `AutomorphicTwistSetup.localFactors` | `Langlands.Automorphic.AssociatedGammaAutomorphicFamily` |
| `IsContragredientOf.heckeDeterminantTwist_inv`, `heckeDeterminantTwist_hasIrreducibleAdmissibleComponents`, `HasRealPlaceParameter.heckeDeterminantTwist`, `HasComplexPlaceParameter.heckeDeterminantTwist` | `Langlands.Automorphic.AssociatedGammaAutomorphicTwist` |
| `FinitePairFactorChoice.exists_engineInputs_cuspidal` | `Langlands.Automorphic.AssociatedGammaCuspidalEquation` |
| `exists_finset_isUnramifiedMatchAt` | `Langlands.Automorphic.AssociatedGammaCommonInputs` |
| `HeckeFunctionalEquation.exists_finset_isUnramifiedAt` | `Langlands.Global.Factors.HeckeFiniteRamification` |
| `HeckeEulerFamily.commonTwistEulerInputs_ofLocalFactors` | `Langlands.Automorphic.AssociatedGammaEulerFamily` |
| `lFactor_eq_of_unramified`, `dualLFactor_eq_of_unramified` | `Langlands.Automorphic.AssociatedGammaOutsideMatch` |
| `ArithmeticTwistSetup.exists_engineInputs`, `ArithmeticTwistSetup.finiteFactors_spec` | `Langlands.Automorphic.AssociatedGammaArithmeticFamily` |
| `ramifiedGammaStability_families` | `Langlands.Automorphic.AssociatedGammaRamifiedStability` |
| `outsideGammaStability_families` | `Langlands.Automorphic.AssociatedGammaOutsideStability` |
| `infinityGammaPreservation_families`, `finiteGammaPreservation_families`, `HeckeCharacter.finiteComponent_one` | `Langlands.Automorphic.AssociatedGammaPreservation` |
| `Correspondence.twistedPairData_spec`, `IsTwistedPairData.exists_gamma`, `hasRationalContinuation_pairDataFactors_gamma`, `Correspondence.isCharacterTwist_one`, `Correspondence.IsCharacterTwist.unique` | `Langlands.Automorphic.AssociatedGammaTwistedPairData` |
| `IsArithmeticPairLocalFactors.exists_gamma` | `Langlands.Automorphic.AssociatedGammaArithmeticGamma` |
| `localPairClass_dual` | `Langlands.Automorphic.AssociatedTemperedLocalProof` |
| `isPairGammaMatch_of_heckeGammaCertificate` | `Langlands.Automorphic.AssociatedGammaHeckeReduction` |
| `localPairClass_twist_of_trivial`, `reciprocityCharacter_one_apply`, `quasicharacterBase_one`, `isCanonicalFiniteAdditiveComponent_unique`, `exists_localWeilData`, `exists_localSystem` | `Langlands.Automorphic.AssociatedGammaFinal` |
| `CuspidalSpectralPresentation.localComponent_padicClass_eq` | `Langlands.Automorphic.AssociatedPresentationComparison` |
| `IsWeaklyAssociatedClass.presentation` | `Langlands.Automorphic.AssociatedPresentationSpectrum` |
| `presentedContragredientAssociation` | `Langlands.Automorphic.Unramified.ContragredientAssociation` |
| `associatedCentralCharacter` | `Langlands.Automorphic.AssociatedCentralCharacterProof` |
| `Automorphic.cuspidalContragredientExistence` | `Langlands.Automorphic.CuspidalContragredientExistenceProof` |
| `Automorphic.cuspidalDualPresentationExistence` | `Langlands.Automorphic.CuspidalDualPresentationExistenceProof` |
| `Automorphic.cuspidalAllLocalIrreduciblePresentationExistence` | `Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationProof` |
| `Automorphic.CuspidalPairPartialGamma.localGenericity` | `Langlands.Global.Factors.CuspidalPairPartialGammaReduction` |
| `Correspondence.arithmeticPairEpsilonExistence` | `Langlands.Correspondence.ArithmeticPairEpsilonExistenceProof` |
| `principalSeriesPairGammaMatchStatement` | `Langlands.Automorphic.PrincipalSeriesGammaMatchProof` |
| `stableTwistPairGammaMatchStatement` | `Langlands.Automorphic.StableTwistGammaMatchProof` |

## 5. Sources and provenance

The mathematical argument is Henniart's: G. Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455
(`henniart-2000-simple-proof`), §2.3, printed pp.444–445, which refers to G. Henniart, *On the
local Langlands conjecture for GL(n): the cyclic case*, Ann. of Math. 123 (1986), 145–203
(`henniart-1986-cyclic`), Theorem 4.1 and §4.3. The formal route is that of the published
`associatedGamma_of_inputs` (see its Markdown). The restriction to totally complex base fields
follows the operator's Option A. The copies in this module are internal.

## 6. Check

All declarations compile in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` over Library
commit `24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85` with no errors or warnings.
`associatedGammaReductionTC` has level parameters `u uV uP uQ uE`, and its axioms are
`propext`, `Classical.choice` and `Quot.sound`. No existing module is edited.
