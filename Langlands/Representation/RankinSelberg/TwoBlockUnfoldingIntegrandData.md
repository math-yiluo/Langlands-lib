# The integrand of the first Section 4.6 unfolding

Module `Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData`,
namespace `Langlands.RankinSelberg.TwoBlockUnfolding`.

Author: Worker 778.

This module is a definitions unit for the first unfolding in JPSS (1983),
Section 4.6. It constructs the actual scalar function
`[g]_H ↦ W(g) f[g; e, e] Φ(ηg)` on the published intermediate quotient
`H \ GL_(t+1)`, where `H` is the block-diagonal unipotent group (5). It also
proves the basic algebraic laws of this function: block covariance of the
scalar section, left `H`-invariance, the representative formula, the fiber
formula, and the identities for the total fiber integral and the radical
average. These are internal data for the displayed unfolding. They are not a
numbered theorem of the original.

## Source and conventions

Source: Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*
(1983), source ID `jpss-1983-rankin-selberg`, Section (4.6). The printed pages
410–412 are zero-based PDF indices 44–46. No errata note for this source exists
in the project literature.

- On printed page 411, the function `W'` is defined by the Jacquet integral
  (2) of Section 4.6. Substituting it into (4.2.1) gives equation (4):
  `Ψ^m(W, W'; Φ)` is the integral over `N \ G^m` of `Φ(ηg) W(g)` times the
  inner integral over `x` of `f[(1 x; 0 1) g; e, e] θ((1 x; 0 1)) dx`.
- On printed page 412, the source uses that `Φ(η_r v g)` does not depend on
  `v ∈ Ū_Q` and obtains, formally, the integral of `W(g) f[g; e, e] Φ(ηg)`
  over `N_(t_1,t_2) \ G_r^m`. Display (5) defines `N_(t_1,t_2)` as the group
  of matrices `diag(n_1, n_2)` with `n_i ∈ N_(t_i)`. The source then justifies
  the step by compact support of `W(g) Φ(η_r g)` modulo `N_r` and absolute
  convergence of (4). Display (6) is a later disintegration. This module
  treats neither the justification nor (6).

The correspondence with this module is as follows.

| JPSS | Here |
| --- | --- |
| block ranks `t_1`, `t_2` | `m 0 + 1`, `m 1 + 1` |
| total rank `r = t = t_1 + t_2` | `t + 1`, with `h : ∑ i, (m i + 1) = t + 1` |
| `G_r` | `GeneralLinear (t + 1) F.Carrier` |
| `N_r` | `upperUnipotent (t + 1) F.Carrier` |
| `N_(t_1,t_2)`, display (5) | the published `TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier` |
| `diag(n_1, n_2)` | the published `blockEmbedding h F.Carrier n` |
| `N_(t_1,t_2) \ G_r` | the published `BlockQuotient h F.Carrier` |
| `(1 x; 0 1)`, `x ∈ M(t_1 × t_2)` | `TwoBlockJacquet.upperRadical h F.Carrier x` |
| `θ` on `N_r` | `Whittaker.standardCharacter ψ t` |
| `θ((1 x; 0 1))` | `TwoBlockJacquet.positiveKernel ψ x` |
| `W ∈ W(π; ψ)` | `Wtest : RankinSelberg.WhittakerFunctions ψ t` |
| `f`, a section of (4.6.1) | `f : TwoBlockJacquet.Sections F h σ` |
| `f[g; e, e]` | `TwoBlockJacquet.scalarSection (fun i => (ell i).val) f g 1` |
| `Φ(ηg)`, `η = (0, …, 0, 1)` | `Φ (RankinSelberg.lastRow g)` |
| `W'(g)`, (2) of Section 4.6 | `TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μ f g` |

The source's sections take values in `W(σ_1; ψ̄) ⊗ W(σ_2; ψ̄)`, and
`f[g; e, e]` evaluates the two Whittaker functions at the identity. Evaluation
at the identity of a `ψ̄`-Whittaker function is a functional with the inverse
standard character. Here the two block representations are abstract, and this
evaluation is replaced by arbitrary actual inverse-character forms
`ell i : Whittaker.glInverseFunctionals ψ (m i) (σ i)`. The scalar section
contracts `f(g)` with `ℓ_0 ⊗ ℓ_1` at the Levi identity `1`, which is the
source's `(e, e)`.

## Hypotheses

Throughout, `p` is a prime, `F : PadicField.{uF} p` is a canonical `p`-adic
field with its canonical topology `F.canonicalTopologicalData.topology`,
`t : ℕ`, `m : Fin 2 → ℕ`, `h : ∑ i, (m i + 1) = t + 1`, `W i : Type uW` are
complex modules, and `σ i` is any actual representation of
`GeneralLinear (m i + 1) F.Carrier` on `W i`. The section `f` is any element
of the published lower normalized induction carrier
`TwoBlockJacquet.Sections F h σ`.

- `ψ` is any `HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`. That
  structure includes continuity and nontriviality (field `nontrivial`), as
  the task requires. No construction or proof here uses the nontriviality
  field.
- The forms `ell i` are any elements of the inverse-character spaces. Zero
  forms are allowed.
- The module assumes no smoothness of `σ i`, no irreducibility, no full
  Whittaker type, no convergence and no nonvanishing.
- `Wtest` is any element of `RankinSelberg.WhittakerFunctions ψ t`, the
  functions with `W(n g) = θ(n) W(g)` for `n ∈ N_r`. No smoothness or local
  constancy is assumed.
- `Φ` is any element of
  `HarmonicAnalysis.SchwartzBruhat (Fin (t + 1) → F.Carrier)`.

## Block covariance of the scalar section (section `Covariance`)

- `scalarSection_blockEmbedding_mul ell f n g`: for
  `n : BlockUnipotents m F.Carrier` and every `g`,
  `f[diag(n_0, n_1) g; e, e] = (∏ i, ψ⁻¹(n_i)) f[g; e, e]`, where `ψ⁻¹(n_i)` is
  `inverseStandardCharacter ψ (m i) (n i)`. The proof uses the published
  `TwoBlockDeformation.sectionEval_leviEmbedding_mul`. Its modulus hypothesis
  comes from `determinantNorm_eq_one_of_mem_upperUnipotent`. Then the published
  `tensorContraction_blockTensor` extracts the product of the inverse
  characters from the block tensor.
- `inverseStandardCharacter_blockEmbedding n`: this product is the ambient
  inverse standard character of `diag(n_0, n_1)` in `N_r`. The proof applies
  the published `inverseStandardCharacter_eq_prod`. The two diagonal blocks of
  `diag(n_0, n_1)` are `n_0`, `n_1`, by the published
  `unipotentLevi_blockEmbedding`. Its corner entry vanishes, by
  `blockEmbedding_index_zero_one`, so the corner factor is `1`.
- `scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter ell f n g`:
  the combination,
  `f[diag(n_0, n_1) g; e, e] = θ(diag(n_0, n_1))⁻¹ f[g; e, e]`.

## The scalar function and its descent (section `Integrand`)

- `groupIntegrand ell f Wtest Φ g` is the function on `GL_(t+1)`:

  ```text
  Wtest.val g * TwoBlockJacquet.scalarSection (fun i => (ell i).val) f g 1 *
    Φ (RankinSelberg.lastRow g)
  ```

  `groupIntegrand_def` unfolds it.
- `groupIntegrand_blockUnipotent_mul`: for every `u ∈ H` and every `g`, the
  value at `u g` equals the value at `g`. Write `u = diag(n_0, n_1)`. The
  standard covariance of `Wtest` gives `W(u g) = θ(u) W(g)`. The covariance
  above gives `f[u g; e, e] = θ(u)⁻¹ f[g; e, e]`. The published
  `lastRow_unipotent_mul` gives `lastRow (u g) = lastRow g`. The two
  characters cancel.
- `integrand ell f Wtest Φ : BlockQuotient h F.Carrier → ℂ` is the actual
  quotient descent `QuotientIntegration.descend (blockUnipotent h F.Carrier)`
  of `groupIntegrand`, using the invariance above. No coset representative is
  chosen and no substitute quotient is introduced.
- `integrand_mk ell f Wtest Φ g` (simp lemma), the representative formula:

  ```text
  integrand ell f Wtest Φ [g]_H =
    Wtest.val g * TwoBlockJacquet.scalarSection (fun i => (ell i).val) f g 1 *
      Φ (RankinSelberg.lastRow g)
  ```

## The fiber formula

`integrand_fiberPoint ell f Wtest Φ x g` holds for every rectangle
`x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier` and every `g`:

```text
integrand ell f Wtest Φ (fiberPoint h F.Carrier x g) =
  Wtest.val g * TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x *
    Φ (RankinSelberg.lastRow g)
```

Here `fiberPoint h F.Carrier x g = [u(x) g]_H` with `u(x) = upperRadical x`.
The published raw integrand is
`TwoBlockJacquet.integrand ψ ell f g x = f[u(x) g; e, e] · positiveKernel ψ x`.
The standard covariance of `Wtest` on `u(x) ∈ N_r`
(`upperRadical_mem_upperUnipotent`) gives `W(u(x) g) = θ(u(x)) W(g)`. The
published `positiveKernel_eq_superdiagonal_upperRadical` identifies
`θ(u(x))` with `positiveKernel ψ x = ψ(x_(m 0, 0))`. This is the source's
`θ((1 x; 0 1))` with its positive sign. No inverse or conjugate kernel occurs
in this formula. Finally `lastRow (u(x) g) = lastRow g`.

## The fiber integral and the radical average

Fix any measurable structure on `F.Carrier`. The rectangle carries Mathlib's
product measurable structure.

- `fiberIntegral_integrand ell f Wtest Φ μ g`: for every measure `μ` on the
  rectangle and every `g`,

  ```text
  fiberIntegral F h μ (integrand ell f Wtest Φ) g =
    Wtest.val g * TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μ f g *
      Φ (RankinSelberg.lastRow g)
  ```

  Both sides are total Bochner integrals: the published `fiberIntegral` on the
  left, and `jacquetFunction`, the Bochner integral of the raw integrand
  against the same `μ`, on the right. The proof applies the fiber formula
  pointwise and moves the constants `Wtest.val g` and `Φ (lastRow g)` out of
  the integral with Mathlib's `integral_mul_const` and `integral_const_mul`.
- `radicalAverage_integrand_mk ell f Wtest Φ`: for a Borel structure on the
  canonical field, every additive Haar measure `μ` on the rectangle and every
  `g`,

  ```text
  radicalAverage F h μ (integrand ell f Wtest Φ) [g]_N =
    Wtest.val g * TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μ f g *
      Φ (RankinSelberg.lastRow g)
  ```

  This uses the published `radicalAverage_mk` and the previous identity.

**Limit of these identities.** They are identities of total Bochner
integrals and hold with no integrability premise. Multiplication by a fixed
complex constant preserves integrability when the constant is nonzero. When
the constant is zero, both sides are zero. So the two integrals agree whether
or not the integrands are integrable. When the raw Jacquet integrand is not
integrable, both sides are `0` by the Bochner convention. These identities
prove no convergence.

## What is not asserted

This module asserts none of the following:

- local constancy or smoothness of an arbitrary `Wtest`;
- compact support of `W(g) Φ(lastRow g)` on a determinant slice modulo `N_r`;
- absolute integrability, convergence or measurability of `integrand`, of the
  raw Jacquet integrand or of their products;
- a quotient-measure tower identity relating integrals over `H \ G`, `N \ G`
  and the rectangle;
- equality of the two outer integrals, over `N \ G^m` and over
  `N_(t_1,t_2) \ G_r^m`;
- the disintegration (6) or the formula (7).

These are separate analytic obligations. The module contains no functional
equation and no factor statement, and it changes no existing Library pair.
