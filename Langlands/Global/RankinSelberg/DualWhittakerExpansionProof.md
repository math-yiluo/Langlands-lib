# Proof of the Whittaker expansion of the dual cusp forms

This module proves `Langlands.Global.RankinSelbergGlobal.DualCuspidalWhittakerExpansionStatement`
(module `Langlands.Global.RankinSelberg.DualWhittakerExpansionStatement`). The proof is the
theorem

```
theorem Langlands.Global.RankinSelbergGlobal.dualCuspidalWhittakerExpansionStatement_proof :
    DualCuspidalWhittakerExpansionStatement.{u}
```

It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Statement proved

Let `F : Type u` be a number field with `𝔸_F/F` compact, let `r : ℕ`, and let
`T : CuspidalOperatorRealization F r` be an actual cuspidal realization of `GL_(r+1)`. Then
`DualCuspidalWhittakerExpansion F T` holds. Fix a standard additive character `ψ` and a vector
`v`. Write `φ = cuspFunction F T v` and `W = cuspWhittaker F T ψ v`, and write
`φ̃ = dualFunction F (r + 1) φ` and `W̃ = dualFunction F (r + 1) W`
(`dualFunction f (g) = f(w ᵗg⁻¹)`). Then:

1. for every `g`, `q ↦ ‖W̃(cornerAdelicPoint F r q.out * g)‖` is summable over
   `N_r(F) \ GL_r(F)`, and `q ↦ W̃(cornerAdelicPoint F r q.out * g)` has sum `φ̃(g)`;
2. for every compact set `C`, the partial sums `g ↦ Σ_(q ∈ s) ‖W̃(cornerAdelicPoint F r q.out * g)‖`
   converge uniformly on `C` to `g ↦ Σ' q, ‖W̃(cornerAdelicPoint F r q.out * g)‖` along the
   filter `atTop` of finite sets `s`.

This is J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §1, Theorem 1.1
(printed p.200; source `cogdell-2004-analytic-theory-gln`), applied to the dual cusp form `φ̃`
and the character `ψ⁻¹`, as the statement's Markdown explains.

## Dependencies

The proof is built on the Whittaker expansion core of Worker 758 (Task 7123, candidate
`c666ae41-20e6-46d3-a426-0db00338a35f`), the modules
`Langlands.Global.RankinSelberg.WhittakerExpansionCore.*`. It uses these results from them:

- `whittaker F r ψ f`, the `ψ`-Whittaker function of `f` with all simple-root coefficients `1`
  (an abbreviation of the Library `generalLinearWhittakerFunction`), and the majorant property
  `HasWhittakerMajorants` (module `Interface`);
- `whittakerMajorantsStatement_proof` (module `WhittakerStep`): every function of a
  `WhittakerDecayClass` has, at every level `j ≤ r` and on every compact set, a summable majorant
  of its Whittaker terms;
- `hasSum_whittaker_of_levelPropsB` (module `ExpansionInduction`): a continuous function that is
  left invariant under `GL_(r+1)(F)`, has the level-`r` cuspidality properties
  (`CuspidalWhittaker.LevelPropsB`) and has summable Whittaker terms at every level is the sum of
  its Whittaker expansion;
- `cuspSpace`, `cuspDerivative`, `cuspEquiv`, `coe_cuspEquiv`, `cuspFunction_apply_eq` and
  `whittakerDecayClass_cuspSpace` (module `ExpansionRealization`): the cusp functions of `T` form
  a `WhittakerDecayClass`.

It also uses two new helper modules of this proof, each with its own Markdown file:

- `Langlands.Global.RankinSelberg.DualWhittakerCore.DualCuspidal`: the function `g ↦ f(ᵗg⁻¹)`
  (`transposeDual f`) of a cuspidal function `f` is cuspidal (`isCuspidal_transposeDual`);
- `Langlands.Global.RankinSelberg.DualWhittakerCore.DualDecay`: if `(V, R)` is a
  `WhittakerDecayClass`, then so is the space `iotaSpace V` of the functions `f ∘ ι`, with
  `ι(g) = ᵗg⁻¹` (`whittakerDecayClass_iotaSpace`).

Library results used directly: `UnequalAnalytic.dualFunction_eq` (`φ̃ = φ ∘ ι` for a left
`GL(F)`-invariant `φ`), `UnequalAnalytic.adelicEquiv_iota`, `cuspFunction_rational_mul`,
`continuous_dualCuspFunction`, `dualCuspFunction_rational_mul`,
`dualCuspWhittaker_eq_setIntegral` (module `UnfoldingDual`),
`subgroupCharacterCoefficient_eq_setIntegral` (module `UnfoldingCoefficient`),
`isStandardAdditiveCharacter_inv`, `genericCharacter_rational_mul`,
`continuous_genericCharacter`, `genericCharacter_inv`, `genericCharacter_inv_eq_inv`,
`padRational_eq_cornerAdelicPoint`, `CuspidalWhittaker.levelProps_top` and
`OperatorRealization.constantTerm_eq_zero`. From Mathlib: `tendstoUniformlyOn_tsum`, the
Weierstrass M-test.

## The proof

All results below are in namespace `Langlands.Global.RankinSelbergGlobal.Unfolding`. The file
sets `backward.isDefEq.respectTransparency false` and declares the same local instances as
`ExpansionRealization` (affineness and smoothness of the group schemes, and `AddCommGroup`
instances `Submodule.addCommGroup` for Library function spaces). These are elaboration settings
and do not change any statement.

1. **The dual cusp function** (section `DualCuspFunction`).
   - `cuspFunction_rational_point` restates `cuspFunction_rational_mul` for a rational point
     `AdelicGroupPoints.rational c`.
   - `dualCuspFunction_eq_iota`: `φ̃(x) = φ(ι x)`. This is the Library
     `UnequalAnalytic.dualFunction_eq`: the long Weyl element is rational and `φ` is left
     invariant under rational points.
   - `coe_iotaSpaceEquiv_cuspEquiv`: `φ̃` is the function of the element
     `iotaSpaceEquiv (cuspEquiv v)` of `iotaSpace (cuspSpace T)`.
   - `hasWhittakerMajorants_dualCuspFunction`: for every standard `ψ`, `φ̃` has the majorants
     `HasWhittakerMajorants F r ψ φ̃`. By the previous item this is
     `whittakerMajorantsStatement_proof` applied to the decay class
     `whittakerDecayClass_iotaSpace (whittakerDecayClass_cuspSpace F T)`.
   - `dualCuspWhittaker_eq_whittaker`: `W̃(x) = whittaker F r ψ⁻¹ φ̃ (x)`. The Library
     `dualCuspWhittaker_eq_setIntegral`, applied to the standard character `ψ⁻¹` and rewritten
     with `(ψ⁻¹)⁻¹ = ψ`, writes `W̃(x)` as the mass normalizer times
     `∫_(m ∈ D) φ̃(m x) (θ_(ψ⁻¹)(m))⁻¹ dm`. Here `D` is the chosen fundamental domain of `N(F)` in
     `N(𝔸)` and `θ_ψ` is the generic character. The Library
     `subgroupCharacterCoefficient_eq_setIntegral` writes the `ψ⁻¹`-Whittaker coefficient of
     `φ̃` at `x` as the same normalizer times `∫_(m ∈ D) φ̃(m x) conj(θ_(ψ⁻¹)(m)) dm`. The two
     integrands agree, since `(θ_(ψ⁻¹)(m))⁻¹ = θ_ψ(m) = conj(θ_(ψ⁻¹)(m))`
     (`genericCharacter_inv_eq_inv`, `genericCharacter_inv` and `|ψ| = 1`).
   - `levelPropsB_dualCuspFunction`: `g ↦ φ̃(homeo⁻¹ g)` has the level-`r` properties, where
     `homeo` is the Library homeomorphism from the group-scheme points to `AdelicGL F (r + 1)`.
     This function is `transposeDual` of the realized vector `T.realization.toContinuous v`. That
     vector is cuspidal (`constantTerm_eq_zero`), so its dual is cuspidal
     (`isCuspidal_transposeDual`), and `CuspidalWhittaker.levelProps_top` gives the properties.
2. **The expansion** (`dualCuspidalWhittakerExpansion`). Fix `ψ` and `v`, and let `ψ⁻¹` be the
   inverse character, which is standard.
   - From the majorants at the singleton `{x}`, the Whittaker terms of `φ̃` for `ψ⁻¹` are
     absolutely summable at every level `k ≤ r` and every point (`hsum`).
   - By `dualCuspWhittaker_eq_whittaker` and `padRational_eq_cornerAdelicPoint`, each term
     `W̃(cornerAdelicPoint q.out * x)` of the target is the level-`r` Whittaker term of `φ̃` for
     `ψ⁻¹` (`hterm`).
   - Clause 1, summability: `hsum` at level `r`, rewritten with `hterm`.
   - Clause 1, sum: `hasSum_whittaker_of_levelPropsB` applied to `φ̃` and `ψ⁻¹`, with continuity
     `continuous_dualCuspFunction`, left invariance `dualCuspFunction_rational_mul`, the level-`r`
     properties `levelPropsB_dualCuspFunction` and `hsum`, rewritten with
     `dualCuspWhittaker_eq_whittaker`.
   - Clause 2: for compact `C`, the majorants at level `r` give a summable `b` with
     `‖W̃(cornerAdelicPoint q.out * x)‖ ≤ b q` for all `x ∈ C` (through `hterm`). The Weierstrass
     M-test `tendstoUniformlyOn_tsum`, applied to the real functions
     `x ↦ ‖W̃(cornerAdelicPoint q.out * x)‖`, gives the uniform convergence on `C`.
3. **The statement.** `dualCuspidalWhittakerExpansionStatement_proof` is
   `fun F _ _ _ _ T => Unfolding.dualCuspidalWhittakerExpansion F T`.

The route does not use the Library statements `WhittakerExpansionStatement` or the abstract
contragredient existence results. The cuspidality and the decay properties of `φ̃` are proved
directly, from those of `φ`, by the change of variables `g ↦ ᵗg⁻¹`.
