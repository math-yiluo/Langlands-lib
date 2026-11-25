# Cusp forms form a two-sided ideal of the Hecke algebra of `GL_n(F)`

Lean module: `Langlands.BaseChange.CuspFormConvolutionStatement`, namespace
`Langlands.BaseChange`.

This module defines one proposition, `CuspFormConvolutionStatement.{u} : Prop`. It is a
statement only: nothing here proves it, and no declaration assumes it.

## Statement

For every field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]` and Mathlib's
`[IsNonarchimedeanLocalField F]`, and every `n : ℕ`, give `GL_n(F)` (the Library's
`GeneralLinear n F`) its Borel σ-algebra (`letI : MeasurableSpace _ := borel _` with the
corresponding `BorelSpace` instance). Then for every Haar measure `μ` on `GL_n(F)`
(`[μ.IsHaarMeasure]`) and all `f g : SchwartzBruhat (GL_n(F))` (locally constant compactly
supported complex functions), with `f * g` the Library's `Hecke.TestFunction.convolution μ f g`,
`(f * g)(x) = ∫ f(y) g(y⁻¹ x) dμ(y)`:

- if `g` satisfies `HasVanishingConstantTerms` (definition 1 of `Langlands.BaseChange.CuspForm`),
  so does `f * g`;
- if `f` satisfies `HasVanishingConstantTerms`, so does `f * g`.

So the cusp forms form a two-sided ideal of the Hecke algebra `C^∞_c(GL_n(F))` with the
convolution product. Both clauses are about the underlying functions
`(g : GL_n(F) → ℂ)` and `(Hecke.TestFunction.convolution μ f g : GL_n(F) → ℂ)`. The measure
`μ` is quantified; none is chosen or normalized.

## Why it holds (not formalized)

Let `B` be a block shape with `2 ≤ B.length`, `U = B.unipotentSubgroup F` and `ν` a Haar measure
on `U`. Since `f * g` is again locally constant with compact support (the Library's
`Hecke.TestFunction.convolution` is valued in `SchwartzBruhat`), each `u ↦ (f * g)(x u y)` is
continuous with compact support on the closed subgroup `U`, hence `ν`-integrable.

- If `g` is a cusp form: `∫_U (f * g)(x u y) dν(u) = ∫_G f(z) (∫_U g(z⁻¹ x u y) dν(u)) dμ(z) = 0`,
  by Fubini for the continuous compactly supported integrand `(u, z) ↦ f(z) g(z⁻¹ x u y)` on
  `U × G`, and the cusp-form property of `g` at `(z⁻¹ x, y)`.
- If `f` is a cusp form: the left invariance of `μ` gives
  `(f * g)(x u y) = ∫_G f(x u w) g(w⁻¹ y) dμ(w)` (substitute `z = x u w`), and then
  `∫_U (f * g)(x u y) dν(u) = ∫_G g(w⁻¹ y) (∫_U f(x u w) dν(u)) dμ(w) = 0` by Fubini and the
  cusp-form property of `f` at `(x, w)`.

The two-sided translations in definition 1 are exactly what makes both arguments work.

## Use

The global comparison of cyclic base change evaluates the simple trace formula and its twisted
form on test functions with a cusp form at one place (Henniart-Lemaire 2011,
II.6.3, printed p. 120, condition `c_{v₁}(f)`; II.6.4, printed p. 121, the twisted condition
`c^σ_{v₁}(φ)`). This statement lets the comparison convolve such functions with Hecke operators
without losing the condition at the cuspidal place. The companion statements (separate
modules) are
`SplitTensorCuspFormStatement` (passage from `GL_n(F)` to `GL_n(F^l)` at a split place),
`SupercuspidalCuspFormStatement` (a cusp form isolating a given supercuspidal representation)
and `SupercuspidalExistenceStatement` (such representations exist).

## Hypotheses

No `CharZero F` hypothesis is needed or assumed: the argument above works over every
nonarchimedean local field. `IsNonarchimedeanLocalField` bundles a valuative topology, local
compactness and a nontrivial valuation, so finite extensions of `ℚ_p` and Laurent-series fields
`𝔽_q((t))` are both included.

## Sources

- Henniart-Lemaire 2011 (`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`),
  Chapter II, §II.6.3, printed p. 120 (PDF p. 128), and §II.6.4, printed p. 121 (PDF p. 129):
  the conditions `c_{v₁}(f)` and `c^σ_{v₁}(φ)` of the simple trace formula and its twisted form.
