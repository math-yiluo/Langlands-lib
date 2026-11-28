# The test functions `1_{I⁺} · ψ(λ_r)` and their vanishing constant terms

Lean module: `Langlands.Representation.AffineGeneric.TestFunction`, namespace
`Langlands.AffineGeneric`.

Let `F` be a nonarchimedean local field with residue field `k`, `ϖ : Fˣ`, `ψ` a complex additive
character of `k` and `r : Fin (m + 1) → k`.

## Declarations

- `groupCoord_eventuallyEq`, `affineForm_eventuallyEq`: the coordinates `aᵢ(g - 1)` and the
  form `λ_r(g)` are locally constant in `g` by `resOf_eventuallyEq`.
- `testFunction ϖ ψ r = 1_{I⁺} · ψ(λ_r)` takes the value `ψ(λ_r(g))` on `I⁺` and is zero
  off `I⁺` (`testFunction_of_mem`, `testFunction_of_not_mem`).
- `isLocallyConstant_testFunction`, `hasCompactSupport_testFunction`: `I⁺` is open and compact,
  so `testFunction ϖ ψ r` is locally constant with compact support.
- `affineGenericTest ϖ ψ r : SchwartzBruhat (GeneralLinear (m + 1) F)`, the same function as an
  element of `C_c^∞(GL_{m+1}(F))`, with `affineGenericTest_apply`.

## Translation and vanishing constant terms

For a uniformizer `ϖ` (`Iwasawa.IsUniformizingElement`), the restriction `ψ ∘ λ_r` to `I⁺`
is a character by `affineForm_mul`. Write `f = testFunction ϖ ψ r`.

- `testFunction_mul_left`, `testFunction_mul_right`: for `z ∈ I⁺`,
  `f(z g) = ψ(λ_r(z)) f(g)` and `f(g z) = f(g) ψ(λ_r(z))`, by `affineForm_mul`.
- `hasVanishingConstantTerms_testFunction` (**cuspidality**): if `ψ ≠ 1` and every `rᵢ ≠ 0`,
  then `testFunction ϖ ψ r` satisfies `BaseChange.HasVanishingConstantTerms`: for every block
  shape `B` with at least two blocks, every Haar measure on its unipotent radical `U` and all
  `x, y`, the function `u ↦ f(x u y)` is integrable on `U` and its integral is `0`.

**Proof of cuspidality.** Integrability holds because `u ↦ f(x u y)` is continuous with compact
support on the closed subgroup `U`. Choose `t` with `ψ(t) ≠ 1`, and by
`exists_unipotent_affineForm_eq` choose `u₀ ∈ U` with `z = x u₀ x⁻¹ ∈ I⁺` and `λ_r(z) = t`. Left
invariance of the Haar measure (`integral_mul_left_eq_self`) and
`x u₀ u y = z (x u y)` give `I = ψ(t) I` for the integral `I`, by `testFunction_mul_left`.
Hence `(1 - ψ(t)) I = 0` and `I = 0`.

## Origin

For a uniformizer `ϖ`, `m ≥ 1`, `ψ ≠ 1` and every `rᵢ ≠ 0`, `ψ ∘ λ_r` is an affine
generic character of `I⁺`. The test function uses its extension by zero. The comparison
with the character formulas and compact inductions of Knightly–Li and Gross–Reeder is in
[Genericity](Genericity.md#origin).

For `m = 0` and a uniformizer `ϖ`, the character on `I⁺ = 1 + 𝔭` is
`g ↦ ψ(r₀ res(ϖ⁻¹ (g - 1)))`. It factors through the principal-unit homomorphism
`g ↦ res(ϖ⁻¹ (g - 1))` to `k`, which has kernel `1 + 𝔭²`. The root system of `GL_1` is empty.
The vanishing constant term condition is vacuous, since no block shape of total size `1`
has two blocks.
