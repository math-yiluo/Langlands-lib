# The smooth contragredient is the nondegenerate Hecke dual

Worker 280 proves exactly
`Langlands.Hecke.ContragredientHeckeDualStatement.{u, v}` in
`contragredientHeckeDual`. The group universe `u` and representation-space
universe `v` remain independent. The hypotheses are precisely the published
statement's Hausdorff locally compact nonarchimedean group, Borel measurable
structure, left Haar measure, and smooth complex representation. There is no
unimodularity assumption. The statement and its import closure are unchanged.

## Source and provenance

The target is Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, III.1.6, printed p.61 / PDF p.67, in the paragraph
identifying the smooth contragredient with the nondegenerate dual of I.4.1.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The following helper constructions are internal components of a proof of that
published statement. They do not introduce additional source claims or change
Renard's duality conventions. This proof concerns the Hecke module comparison;
it does not assert the subsequent lemma for all compactly supported distributions.

## Implemented proof

The construction retains the actual published smooth dual, Hecke action, and
`NonUnitalModuleDual.dualObject`. Write `ρ` for the smooth representation and
`π(f)` for `heckeAction μ ρ hρ f`.

1. **Transpose for arbitrary Haar measure.**
   `heckeAction_smoothDualPairing_haar` evaluates the integrated action against a
   linear functional using `integratedAction_dual`. It forms the actual
   Schwartz–Bruhat test
   `b(g) = f(g⁻¹) ℓ(ρ(g)v)`. Smoothness makes the matrix coefficient locally
   constant, and the inverted test factor gives compact support. Applying the
   published `integral_inv_test` gives
   `∫ b(g⁻¹) dμ(g) = ∫ b(g) haarScale(g) dμ(g)`.
   Rearrangement yields
   `(π̃(f)ℓ)(v) = ℓ(π(haarInversion μ f)v)`.
   The weight is Mathlib's modular character, as a complex character, exactly
   as in the published `haarInversion` on Haar densities.

2. **Absorption of subgroup actions.**
   `heckeAction_group_of_rightInvariant` proves that if `f(xk) = f(x)` for a
   compact open subgroup `K`, then `π(f)ρ(k)v = π(f)v` for `k ∈ K`. It separates
   vectors by arbitrary complex-linear functionals `L`, packages
   `b(x) = f(x)L(ρ(x)v)` as a Schwartz–Bruhat test, and applies
   `integral_mul_right_test`. The modular character is one on `K`, so the
   translation introduces no scalar factor.

3. **Comparison of the full duals.**
   The I.4.1 construction uses complex scalars recovered from the nondegenerate
   Hecke action. `heckeFullDualEquiv` compares this full dual with the original
   complex-linear dual. `NonUnitalModule.ofLinearEndHom_isScalarTower` supplies
   compatibility of the original scalars with the actual Hecke action, and
   `NondegenerateScalars.scalarMul_eq_of_compatible` identifies the recovered
   scalar multiplication with the original one. Both directions keep the
   entire underlying function unchanged; the two application lemmas state
   their evaluation formulas.

4. **Nondegeneracy equals smoothness.**
   `heckeFullDualEquiv_mem_iff` uses `NonUnitalModuleDual.mem_dual_iff` to express
   membership as `φ(π(e)v) = φ(v)` for a Hecke idempotent `e`. For a member,
   `TestFunction.commonCompactOpenBiInvariance` gives a compact open subgroup
   under which `e` is right invariant. Step 2 applied to `k⁻¹` proves
   `φ(ρ(k⁻¹)v) = φ(v)`, which is smoothness for the original dual group action.
   Conversely, a smooth functional is fixed by some compact-open normalized
   indicator in the smooth contragredient, by
   `exists_normalizedIndicator_fixes`. Haar inversion fixes that indicator by
   `haarInversion_normalizedIndicator`. Step 1 then gives precisely the
   idempotent fixing condition for membership in the nondegenerate dual.

5. **The required equivalence and action.**
   `smoothHeckeDualEquiv` restricts the full-dual additive equivalence using
   step 4. `smoothHeckeDualEquiv_apply` records its unchanged evaluation.
   `contragredientHeckeDual` uses this equivalence for the given `SmoothRep`.
   The evaluation clause is definitional. For the action clause it takes
   equality of underlying functionals and evaluates at an arbitrary vector.
   The right dual action is definitionally precomposition with the original
   Hecke action, so step 1 proves the required equality
   `e(π̃(T)ℓ) = op (haarInversion μ T) • e(ℓ)`.

## Verification

The proof module compiles in the task's prepared Lean environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. Its final declaration has the exact
published proposition as its type; all helpers are proved from published
imports. Independent semantic review and submission validation are required
for acceptance.
