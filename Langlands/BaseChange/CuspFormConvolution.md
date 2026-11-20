# Cusp forms form a two-sided ideal of the Hecke algebra of `GL_n(F)`

Lean module: `Langlands.BaseChange.CuspFormConvolution`, namespace `Langlands.BaseChange`.
Author: Worker 1020, for Task 7593.

The theorem `Langlands.BaseChange.cuspFormConvolution` proves the published proposition
`Langlands.BaseChange.CuspFormConvolutionStatement` (module
`Langlands.BaseChange.CuspFormConvolutionStatement`, Task 7457) at an arbitrary universe `u`.
Its type is exactly `CuspFormConvolutionStatement.{u}`. It adds no hypothesis (in particular no
`CharZero F`), assumes no unproved proposition and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

Let `F` be a nonarchimedean local field (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`), `n : ℕ`, `G = GL_n(F)` (the Library's `GeneralLinear n F`)
with its Borel σ-algebra, `μ` a Haar measure on `G` and `f g` test functions
(`SchwartzBruhat G`). Write `f * g` for `Hecke.TestFunction.convolution μ f g`, so
`(f * g)(x) = ∫ f(y) g(y⁻¹ x) dμ(y)`. Then:

- if `g` satisfies `HasVanishingConstantTerms`, so does `f * g`;
- if `f` satisfies `HasVanishingConstantTerms`, so does `f * g`.

`HasVanishingConstantTerms` (module `Langlands.BaseChange.CuspForm`) and
`Hecke.TestFunction.convolution` (module `Langlands.Representation.Hecke.Convolution`) are used
as published; this module defines no new notion of constant term or convolution.

## General lemmas

Section `General` works with an arbitrary topological group `G` (`[Group G] [TopologicalSpace G]
[IsTopologicalGroup G]`) with a measurable structure making it a Borel space, a subgroup
`U ≤ G` whose carrier is closed (`hU : IsClosed (U : Set G)`), and a measure `ν` on `U` (subspace
σ-algebra) that is finite on compact sets. No Hausdorff, local compactness, second countability
or σ-finiteness hypothesis is used.

1. `isClosedEmbedding_mul_coe_mul hU x y`: `u ↦ x * u * y` is a closed embedding `U → G`. It is
   the inclusion of the closed subgroup (`IsClosed.isClosedEmbedding_subtypeVal`) followed by the
   homeomorphism `g ↦ x * g * y`.
2. `integrable_comp_mul_coe_mul hU ν φ x y`: for a test function `φ`, `u ↦ φ (x * u * y)` is
   `ν`-integrable. It is continuous, and it has compact support because a compactly supported
   function composed with a closed embedding has compact support
   (`HasCompactSupport.comp_isClosedEmbedding`). Mathlib's
   `Continuous.integrable_of_hasCompactSupport` then applies.
3. `integral_convolution_eq_zero_of_right μ hU ν f g hg x y` (`μ` finite on compact sets): if
   `g` is cuspidal along `U` (`HarishChandraSchwartz.IsUnipotentCuspidal ν g`, that is,
   `∫_U g(a u b) dν(u) = 0` for all `a b`), then `∫_U (f * g)(x u y) dν(u) = 0`. After unfolding
   the convolution (`Hecke.TestFunction.convolution_apply`), Mathlib's compact-support Fubini
   theorem `integral_integral_swap_of_hasCompactSupport` gives
   `∫_U ∫_G f(z) g(z⁻¹ (x u y)) dμ(z) dν(u) = ∫_G ∫_U f(z) g(z⁻¹ (x u y)) dν(u) dμ(z)`.
   That theorem needs only that both measures are finite on compact sets, and that the integrand
   `(u, z) ↦ f(z) g(z⁻¹ x u y)` on `U × G` is continuous with compact support. Its support lies in
   the compact set `e⁻¹(supp f · supp g) × supp f`, where `e u = x u y` is the closed embedding of
   step 1 and supports of test functions are compact (`Hecke.TestFunction.isCompact_support`):
   if `f(z) ≠ 0` and `g(z⁻¹ x u y) ≠ 0`, then `x u y = z · (z⁻¹ x u y)`. For each `z`, the inner
   integral is `f(z) · ∫_U g((z⁻¹ x) u y) dν(u) = f(z) · 0` (`integral_const_mul` and the
   cuspidality of `g` at `(z⁻¹ x, y)`), so the outer integral vanishes.
4. `convolution_apply_mul_eq μ f g a y` (`μ` left invariant): `(f * g)(a y) =
   ∫_G f(a w) g(w⁻¹ y) dμ(w)`. This is the substitution `z = a w`, by Mathlib's
   `integral_mul_left_eq_self`, and `(a w)⁻¹ (a y) = w⁻¹ y`.
5. `integral_convolution_eq_zero_of_left μ hU ν f g hf x y` (`μ` finite on compact sets and left
   invariant): if `f` is cuspidal along `U`, then `∫_U (f * g)(x u y) dν(u) = 0`. Step 4 with
   `a = x u` rewrites the integrand as `∫_G f(x u w) g(w⁻¹ y) dμ(w)`. The same Fubini theorem
   swaps the integrals. The integrand `(u, w) ↦ f(x u w) g(w⁻¹ y)` is continuous, and its support
   lies in the compact set `e'⁻¹(supp f · L⁻¹) × L`. Here `L = {w | w⁻¹ y ∈ supp g}` is
   compact, being the image of `supp g` under the continuous map `k ↦ y k⁻¹`, and `e' u = x u · 1`
   is the closed embedding of step 1: if `f(x u w) ≠ 0` and `g(w⁻¹ y) ≠ 0`, then `w ∈ L` and
   `x u = (x u w) w⁻¹`. For each `w` the inner integral is
   `(∫_U f(x u w) dν(u)) · g(w⁻¹ y) = 0 · g(w⁻¹ y)` (`integral_mul_const` and the cuspidality
   of `f` at `(x, w)`).

## The main theorem

`cuspFormConvolution` introduces `F`, its instances, `n`, `μ`, the Haar instance and `f g`, and
names the Borel σ-algebra on `GL_n(F)` with its `BorelSpace` instance as in the statement. It
proves `T2Space F` locally with the argument of the Library's `BruhatTits.localField_t2Space`
(give `F` the right uniform structure of its additive group; Mathlib then infers the Hausdorff
property of the valued field). This keeps the module from importing the algebraic-geometry
module that holds that lemma. `T2Space F` is needed for
`GeneralLinear.BlockShape.isClosed_unipotentSubgroup`, which says that `U = B.unipotentSubgroup F`
is closed in `GL_n(F)`.

For each clause, unfold `HasVanishingConstantTerms` for `f * g`: given a block shape `B` with
`2 ≤ B.length` and a Haar measure `ν` on `U = B.unipotentSubgroup F`, the hypothesis on `g`
(respectively `f`) at `B` and `ν` gives cuspidality along `U` (its integrability part is not
needed). Haar measures on `U` and `G` are finite on compact sets.

- Integrability of `u ↦ (f * g)(x u y)`: step 2 applied to the test function `f * g`.
- Vanishing: step 3 for the first clause (`g` a cusp form) and step 5 for the second (`f` a cusp
  form).

The case `n ≤ 1` needs no separate treatment: the argument applies to every block shape.

## Relation to the source route

This is the Fubini computation of the statement's Markdown (section "Why it holds") and of the
task. One difference: σ-finiteness and second countability are not used, because Mathlib's
`integral_integral_swap_of_hasCompactSupport` needs only measures finite on compact sets and a
continuous, compactly supported integrand. The mathematical source of the statement is
Henniart-Lemaire 2011, II.6.3 (printed p. 120), condition `c_{v₁}(f)`.

## Library and Mathlib results used

- `Langlands.BaseChange.CuspFormConvolutionStatement` (target statement).
- `Langlands.BaseChange.HasVanishingConstantTerms` (module `Langlands.BaseChange.CuspForm`).
- `Langlands.HarishChandraSchwartz.IsUnipotentCuspidal`
  (module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalConvolution`).
- `Langlands.Hecke.TestFunction.convolution`, `Langlands.Hecke.TestFunction.convolution_apply`
  (module `Langlands.Representation.Hecke.Convolution`) and
  `Langlands.Hecke.TestFunction.isCompact_support` (module
  `Langlands.Representation.Hecke.TestFunction`).
- `Langlands.HarmonicAnalysis.SchwartzBruhat.continuous`, `.hasCompactSupport`.
- `Langlands.GeneralLinear.BlockShape.isClosed_unipotentSubgroup` (module
  `Langlands.Group.GL.Blocks`).
- Mathlib: `MeasureTheory.integral_integral_swap_of_hasCompactSupport`,
  `MeasureTheory.integral_mul_left_eq_self`, `Continuous.integrable_of_hasCompactSupport`,
  `HasCompactSupport.comp_isClosedEmbedding`, `HasCompactSupport.of_support_subset_isCompact`,
  `Topology.IsClosedEmbedding.isCompact_preimage`, `IsClosed.isClosedEmbedding_subtypeVal`,
  `integral_const_mul`, `integral_mul_const`.
