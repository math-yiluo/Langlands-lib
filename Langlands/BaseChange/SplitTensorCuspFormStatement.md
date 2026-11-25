# Split tensor products of test functions and cusp forms

Lean module: `Langlands.BaseChange.SplitTensorCuspFormStatement`, namespace
`Langlands.BaseChange`.

This module defines one proposition, `SplitTensorCuspFormStatement.{u} : Prop`. It is a
statement only: nothing here proves it, and no declaration assumes it.

## Statement

For every field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]` and Mathlib's
`[IsNonarchimedeanLocalField F]`, all `n l : ℕ` and every family
`φ : Fin l → SchwartzBruhat (GL_n(F))` of locally constant compactly supported functions on
`GL_n(F)` (the Library's `GeneralLinear n F`), with `Fin l → F` carrying the product topology
(Mathlib's `Pi` instances, a commutative topological ring):

- (a) `splitTensor (fun i => φ i)` belongs to
  `HarmonicAnalysis.schwartzBruhatSubmodule (GL_n(Fin l → F))`, that is, it is locally
  constant with compact support on `GL_n(F^l)`;
- (b) for every `i₀ : Fin l`, if `φ i₀` (as a function) satisfies `HasVanishingConstantTerms`
  over `F`, then `splitTensor (fun i => φ i)` satisfies `HasVanishingConstantTerms` over
  `Fin l → F`.

Here `splitTensor` is definition 2 of `Langlands.BaseChange.CuspForm`:
`splitTensor φ g = ∏ i, φ i (g_i)`, with `g_i` the image of `g` under the `i`-th coordinate
projection `F^l → F`. Under `GL_n(F^l) = GL_n(F)^l` it is the tensor product
`φ_0 ⊗ … ⊗ φ_{l-1}`.

## Why it holds (not formalized)

- (a) The map `g ↦ (g_0, …, g_{l-1})` is an isomorphism of topological groups
  `GL_n(F^l) ≅ GL_n(F)^l` (a matrix over `F^l` is an `l`-tuple of matrices over `F`, and the
  topology on units is induced by `g ↦ (g, g⁻¹)`). The tensor product of locally constant
  compactly supported functions on the factors is locally constant with compact support on the
  product. For `l = 0` the group `GL_n(Fin 0 → F)` has one element and `splitTensor` is the
  constant `1`, which is locally constant with compact support.
- (b) For a block shape `B` with `2 ≤ B.length`, `B.unipotentSubgroup (Fin l → F)` corresponds
  to `U(F)^l`, `U = B.unipotentSubgroup F` (the block parabolics of `GL_n(F^l)` are the products
  `P(F) × … × P(F)` of one block parabolic of `GL_n(F)`; see the Markdown of `CuspForm`). A
  Haar measure on `U(F)^l` is a positive multiple of a product `ν_0 ⊗ … ⊗ ν_{l-1}` of Haar
  measures on `U(F)`, and integrability follows from (a). By Fubini,
  `∫ ∏ φ_i(x_i u_i y_i) d(⊗ν_i) = ∏_i ∫ φ_i(x_i u_i y_i) dν_i(u_i)`, whose factor `i₀`
  vanishes because `φ i₀` is a cusp form for the Haar measure `ν_{i₀}`.

## Use

The global comparison for local cyclic base change of prime degree evaluates the simple trace
formula and its twisted form on test functions with a cusp form at one place (Henniart-Lemaire 2011,
II.6.3, printed p. 120, condition `c_{v₁}(f)`; II.6.4, printed p. 121, condition `c^σ_{v₁}(φ)`).
At a place `v` of the base field that splits completely in the cyclic extension `E` of degree
`l`, `E ⊗ F_v = F_v^l` and the test function on `GL_n(E_v) = GL_n(F_v)^l` is a tensor product
(Arthur-Clozel 1989, Chapter 1, §5, printed pp. 48-49, where the σ-twisted orbital integrals of
`φ_1 ⊗ … ⊗ φ_m` are computed through the convolution `φ_1 ∗ … ∗ φ_m`). This statement passes
from `GL_n(F)` to `GL_n(F^l)` at such a place: a cusp form in one factor gives a cusp form on
`GL_n(F^l)`, and the tensor product is again a test function. The companion statements
(separate modules) are
`CuspFormConvolutionStatement` (convolution with Hecke operators), `SupercuspidalCuspFormStatement`
(a cusp form isolating a given supercuspidal representation) and
`SupercuspidalExistenceStatement` (such representations exist).

## Hypotheses

No `CharZero F` hypothesis is needed or assumed. The ring `Fin l → F` is not a field for
`l ≠ 1`; definition 1 is stated for commutative topological rings so that it applies here.

## Sources

- Arthur-Clozel 1989 (`arthur-clozel-1989-base-change`), Chapter 1, §5, printed pp. 48-49
  (PDF pp. 62-63): tensor-product test functions at a place that is not inert.
- Henniart-Lemaire 2011 (`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`),
  Chapter II, §II.6.3, printed p. 120 (PDF p. 128), and §II.6.4, printed p. 121 (PDF p. 129).
