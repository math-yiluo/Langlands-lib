# JPSS Section 6.1: the special `(r+1,1)` tensor integral model

Worker 753 defines the test space, the extended `ρ₀` action, the kernel
matrix and the raw scalar integral of formula (8) in Section 6.1 of
Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*
(Amer. J. Math. 105, 1983), registered as `jpss-1983-rankin-selberg`. The
source is the special case of lower block ranks `(t-1, 1)`. Here
`t = r + 2`, so the inner group is the actual `GL_(r+1)` and the ambient
group is the actual `GL_(r+2)`. The module contains definitions and their
elementary algebraic computation laws only. It proves no convergence, no
membership in an induced Whittaker model, and no local-factor statement.

All declarations are in `Langlands.RankinSelberg`. The canonical p-adic
specializations are in its subnamespace `Langlands.RankinSelberg.Padic`.
The module imports published objects by Lean name:
`rectangularRho0`, `rectangularJoin` and their API from
`Langlands.HarmonicAnalysis.PartialFourierEquiv` and `RectangularFourier`;
`glFunctionals`, `glCoefficientModel` and `glModelFunction` from
`Langlands.Representation.Whittaker.GeneralLinear`;
`GeneralLinear.inverseTranspose` and `GeneralLinear.determinant` from
`Langlands.Group.GL`; `determinantWeight` from `QuotientIntegrals`;
`normalizedAbsoluteValue` from `AnalyticStatement`; and
`generalLinearHaar` from `Measures`. No published declaration is changed.

## The source formulas

On printed page 428 the source lets `ε` be the transpose of the row vector
`η = (0, 0, …, 0, 1)` of length `t - 1`. Its Proposition takes `Ψ` in
`S(t-1 × t; F) ⊗ W(σ₁; ψ)`, "the space of Schwartz functions with values
in `W(σ₁; ψ)`". Formula (8) on printed page 429 reads

```text
W_{Ψ,σ₂}(g) = σ₂α^{(t-1)/2}(det g)
                ∫_{G_{t-1}} (ρ₀(g)Ψ)[h, h^ι ε; h⁻¹] σ₂α^{t/2-1}(det h) dh.
```

Here `α` is the absolute value, `σ₂` is a character of `F^×`, and `ρ₀`
acts on the Schwartz variable, as stated on printed page 428 ("We will use
the same notation for vector-valued functions"). The argument
`[h, h^ι ε; h⁻¹]` evaluates the Schwartz variable at the
`(t-1) × t` matrix `[h, h^ι ε]` and the Whittaker function at `h⁻¹`. By
(0.3.6) on printed page 376, `g^ι = ᵗg⁻¹` is the inverse transpose, not the
transpose. With `t = r + 2`, the outer exponent `(t-1)/2` is `(r+1)/2` and
the inner exponent `t/2 - 1` is `r/2`. The proof of the Proposition
(printed pages 429-431) reduces to pure tensors and uses that an arbitrary
`Ψ` is a finite sum of pure tensors. No erratum for this source is
registered, and none was inferred from the scan.

In Lean, `σ₂` is the supplied quasicharacter `χ` and `α` is the supplied
absolute value `abv`. The source's `σ₁` is the supplied representation
`σ` of `GL_(r+1)(F)` with the specified functional `ℓ`, and `W(σ₁; ψ)` is
its actual coefficient image `glCoefficientModel ψ r σ ℓ`. The source's
Haar measure `dh` is a supplied measure `η` on the generic side and the
shared normalized Haar measure on the p-adic side.

## Parameters

The field is an arbitrary `F : Type uF`. The carrier is an arbitrary
`V : Type uV` with `[AddCommGroup V] [Module ℂ V]`. The universes are
independent. The test space only needs `[Field F] [TopologicalSpace F]`,
and the kernel only needs `[Field F]`. The action and the integrals use
exactly the hypotheses of the published `partialFourierEquiv`:

```text
[Field F] [TopologicalSpace F] [IsTopologicalRing F]
[MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F]
[T2Space F] [TotallyDisconnectedSpace F]
```

The explicit arguments are `ψ : UnitaryAdditiveCharacter F`,
`ν : AdditiveHaarMeasure F`, `hself : IsSelfDual ψ ν`,
`σ : Representation ℂ (GeneralLinear (r + 1) F) V` and
`ℓ : glFunctionals ψ r σ`, with `r : ℕ` implicit. The integrals add
`abv : AbsoluteValue F ℝ`, `χ : Quasicharacter F`, an instance
`[MeasurableSpace (GeneralLinear (r + 1) F)]`, and an explicit
`η : Measure (GeneralLinear (r + 1) F)`. The argument order is

```text
adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ g h
AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η Ψ g
adjacentRankModelIntegral  ψ ν hself σ ℓ abv χ η Ψ g
```

There is no topology, norm or completeness on `V` or on the coefficient
image. There is no smoothness, admissibility, irreducibility,
Whittaker-type or nonvanishing hypothesis on `σ` or `ℓ`; in particular
`ℓ = 0` is allowed. The definitions do not assume that `η` is a Haar
measure, and no measure is chosen silently. Every definition includes
`r = 0`.

## Test space and evaluation

`adjacentRankTestSpace ψ σ ℓ` is an `abbrev` for the algebraic complex
tensor product

```text
SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F) ⊗[ℂ]
  (glCoefficientModel ψ r σ ℓ).toSubmodule.
```

It is an `abbrev` so that the tensor-product module instances apply
directly. `adjacentRankTestBilinear ψ σ ℓ` is the complex-bilinear map,
built with `LinearMap.mk₂`, that sends `(Φ, W)` to the function
`(m, k) ↦ Φ m * glModelFunction ψ r σ ℓ W k`. Here `m` is a rectangular
matrix and `k : GeneralLinear (r + 1) F`.
`adjacentRankTestEvaluation ψ σ ℓ` is the linear map
`TensorProduct.lift (adjacentRankTestBilinear ψ σ ℓ)` into
`Matrix (Fin (r + 1)) (Fin (r + 2)) F → GeneralLinear (r + 1) F → ℂ`.

This is the finite-tensor realization of the source's Schwartz functions
with values in the Whittaker model. A finite tensor `∑ Φⱼ ⊗ Wⱼ` gives the
model-valued Schwartz function `m ↦ ∑ Φⱼ(m) Wⱼ`. Its value at `k` is the
evaluation above. The Whittaker factor is the actual coefficient image of
`ℓ`. It is not replaced by all equivariant functions or by another family
of functions. This module neither proves nor uses injectivity of the
evaluation map; every later statement is phrased through this map.

| Lemma | Content |
| --- | --- |
| `adjacentRankTestEvaluation_tmul` (simp, `rfl`) | `E(Φ ⊗ₜ W) m k = Φ m * glModelFunction ψ r σ ℓ W k` |
| `adjacentRankTestEvaluation_zero` (simp) | `E 0 m k = 0` |
| `adjacentRankTestEvaluation_add` | `E(Ψ₁ + Ψ₂) m k = E Ψ₁ m k + E Ψ₂ m k` |
| `adjacentRankTestEvaluation_smul` | `E(c • Ψ) m k = c * E Ψ m k` |
| `adjacentRankTestEvaluation_sum` | `E(∑ i ∈ S, Ψ i) m k = ∑ i ∈ S, E (Ψ i) m k` |
| `adjacentRankTestEvaluation_sum_tmul` | `E(∑ j, Φ j ⊗ₜ W j) m k = ∑ j, Φ j m * glModelFunction ψ r σ ℓ (W j) k` |

Here `E = adjacentRankTestEvaluation ψ σ ℓ`. Two results reduce claims
about every test tensor to pure tensors:

- `adjacentRankTestSpace_exists_sum_tmul` proves that every `Ψ` equals
  `∑ j : Fin n, Φ j ⊗ₜ W j` for some `n`, `Φ` and `W`. It is Mathlib's
  `TensorProduct.exists_sum_tmul_eq`.
- `adjacentRankTestSpace_induction` (`elab_as_elim`) proves a property `P`
  of every test tensor from `P (Φ ⊗ₜ W)` for all pure tensors and closure
  of `P` under addition. It is Mathlib's `TensorProduct.inductionOn`. In
  the current Mathlib this has no separate zero case, because
  `0 = 0 ⊗ₜ 0`.

## The extended `ρ₀` action

`adjacentRankRho0 ψ ν hself σ ℓ` is a
`Representation ℂ (GeneralLinear (r + 2) F) (adjacentRankTestSpace ψ σ ℓ)`.
Its value at `g` is

```text
TensorProduct.map (rectangularRho0 ψ ν (r + 1) hself g) LinearMap.id.
```

It acts only on the rectangular Schwartz factor. `rectangularRho0` is the
published action. It is built from the chosen `partialFourierEquiv` for the
supplied self-dual scalar Haar `ν`: the forward partial transform uses the
inverse character, and the inverse uses the plus character. No other
Fourier equivalence and no covariance law is assumed. The identity and
multiplication fields are checked on pure tensors with `TensorProduct.ext'`,
where `simp` applies the representation laws of `rectangularRho0`. The
ranks `r + 2` and `r + 1 + 1` agree definitionally.

| Lemma | Content |
| --- | --- |
| `adjacentRankRho0_apply` (`rfl`) | the `TensorProduct.map` formula above |
| `adjacentRankRho0_tmul` (simp, `rfl`) | `ρ(g)(Φ ⊗ₜ W) = rectangularRho0 ψ ν (r + 1) hself g Φ ⊗ₜ W` |
| `adjacentRankRho0_one` (simp) | `ρ(1) Ψ = Ψ` |
| `adjacentRankRho0_mul` | `ρ(g * h) Ψ = ρ(g) (ρ(h) Ψ)` |

Here `ρ = adjacentRankRho0 ψ ν hself σ ℓ`.

## Kernel matrix

`adjacentRankEpsilon F r : Fin (r + 1) → F` is
`Pi.single (Fin.last r) 1`. It is the source's `ε`, the last standard
basis column of length `r + 1 = t - 1`. For `h : GeneralLinear (r + 1) F`,

```text
adjacentRankKernelMatrix h =
  rectangularJoin h.val
    ((GeneralLinear.inverseTranspose (r + 1) F h).val *ᵥ adjacentRankEpsilon F r)
```

is the `(r+1) × (r+2)` matrix `[h, h^ι ε]`, with `h^ι = ᵗ(h⁻¹)` the
published inverse transpose. The column `h^ι ε` is the last column of
`ᵗ(h⁻¹)`, that is, the last row of `h⁻¹` read as a column.

| Lemma | Content |
| --- | --- |
| `inverseTranspose_mulVec_adjacentRankEpsilon` | `(ᵗ(h⁻¹) *ᵥ ε) i = (h⁻¹) (Fin.last r) i` |
| `adjacentRankKernelMatrix_castSucc` (simp) | `adjacentRankKernelMatrix h i j.castSucc = h i j` |
| `adjacentRankKernelMatrix_last` (simp) | `adjacentRankKernelMatrix h i (Fin.last (r + 1)) = (h⁻¹) (Fin.last r) i` |
| `rectangularFirstColumns_adjacentRankKernelMatrix` (simp) | the first block is `h.val` |
| `rectangularLastColumn_adjacentRankKernelMatrix` (simp) | the last column is `fun i => (h⁻¹) (Fin.last r) i` |
| `adjacentRankKernelMatrix_rankZero` | for `h : GeneralLinear 1 F`, the matrix is `!![h 0 0, (h⁻¹) 0 0]` |

So the `i`-th last-column entry is `(h⁻¹)(last, i)`, an entry of the
inverse. It is not the `i`-th last-column entry `h(last, i)` of the plain
transpose `ᵗh`. In the case `r = 0` the
inner group is `GL₁`, the ambient group is `GL₂`, and the kernel is the row
`[h, h⁻¹]`.

## Integrand, convergence and integral

Write `E` for the evaluation and `ρ` for the action above. For
`g : GeneralLinear (r + 2) F` and `h : GeneralLinear (r + 1) F`:

```text
adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ g h =
  E (ρ g Ψ) (adjacentRankKernelMatrix h) h⁻¹ *
    (χ (GeneralLinear.determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)

AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η Ψ g =
  Integrable (fun h => adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ g h) η

adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η Ψ g =
  (χ (GeneralLinear.determinant g) : ℂ) *
    determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
    ∫ h, adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ g h ∂η
```

`GeneralLinear.determinant` takes values in `Fˣ`, and `χ` maps them to
`ℂˣ`, coerced to `ℂ`. `determinantWeight abv g s` is
`(abv (det g) : ℂ) ^ s`, the usual complex power of a nonnegative real.
The two weights are the source's `σ₂α^{t/2-1}(det h)` and
`σ₂α^{(t-1)/2}(det g)` at `t = r + 2`. Both occurrences of `χ` are kept,
and the Whittaker variable is evaluated at `h⁻¹`. The integral is
Mathlib's totalized Bochner integral, so it is `0` when the integrand is
not integrable. It is not a chosen value and does not assume convergence.

The integral on the whole tensor space is deliberately not packaged as a
linear map. Its additivity holds only under integrability hypotheses.

| Lemma | Content |
| --- | --- |
| `adjacentRankModelIntegrand_zero` (simp) | the integrand of `0` is `0` |
| `adjacentRankModelIntegrand_add` | the integrand of `Ψ₁ + Ψ₂` is the sum of the integrands |
| `adjacentRankModelIntegrand_smul` | the integrand of `c • Ψ` is `c •` the integrand |
| `adjacentRankModelIntegrand_sum` | the integrand of a finite sum is the finite sum |
| `adjacentRankModelIntegrand_tmul` (`rfl`) | at `Φ ⊗ₜ W`: `rectangularRho0 ψ ν (r + 1) hself g Φ (adjacentRankKernelMatrix h) * glModelFunction ψ r σ ℓ W h⁻¹ * χ(det h) * determinantWeight abv h (r/2)` |
| `adjacentRankModelConverges_zero` | `0` converges |
| `AdjacentRankModelConverges.add` | convergence of `Ψ₁` and `Ψ₂` at `g` gives it for `Ψ₁ + Ψ₂` |
| `AdjacentRankModelConverges.smul` | convergence of `Ψ` at `g` gives it for `c • Ψ` |
| `adjacentRankModelConverges_sum` | convergence of every summand at `g` gives it for the finite sum |
| `adjacentRankModelIntegral_zero` (simp) | the integral of `0` is `0` |
| `adjacentRankModelIntegral_smul` | the integral of `c • Ψ` is `c *` the integral, with no hypothesis |
| `adjacentRankModelIntegral_add` | additivity at `g`, assuming convergence of both `Ψ₁` and `Ψ₂` at `g` |
| `adjacentRankModelIntegral_sum` | finite additivity at `g`, assuming convergence of every summand at `g` |
| `adjacentRankModelIntegral_tmul` (`rfl`) | the integral at `Φ ⊗ₜ W` as the outer weight times the integral of the pure-tensor integrand |

The integrand laws follow from linearity of the evaluation and of the
action, with `ring` in `ℂ`. The convergence laws are Mathlib's
`integrable_zero`, `Integrable.add`, `Integrable.smul` and
`integrable_finsetSum'`. The integral laws are `integral_add`,
`integral_const_mul` and `integral_finsetSum`, followed by distributing
the outer weight. The scalar law needs no hypothesis because
`integral_const_mul` holds for every function. Together with
`adjacentRankTestSpace_exists_sum_tmul` and the pure-tensor formulas,
these laws reduce later convergence and finite-sum arguments to integrals
of pure tensors.

## Canonical p-adic specializations

For `F : PadicField.{uF} p` with `[Fact p.Prime]`, the subnamespace
`Langlands.RankinSelberg.Padic` sets local instances on `F.Carrier` from
`F.canonicalTopologicalData`: the topology, valuative relation, local
field structure and Hausdorff property. `TotallyDisconnectedSpace` comes
from the nonarchimedean ring structure of the valuation topology, by the
same argument as in the published `TwoBlockRowFourierCompanionStatement`.
The Borel structure is used on `F.Carrier` and on each
`GeneralLinear (n + 1) F.Carrier`. These are the same local instances as
in the published `Langlands.GodementJacquet.Padic` specializations.

The supplied data are `ψ : UnitaryAdditiveCharacter F.Carrier`,
`ν : AdditiveHaarMeasure F.Carrier`, `hself : IsSelfDual ψ ν`, `σ`, `ℓ`
and `χ : Quasicharacter F.Carrier`. The three definitions

```text
Padic.adjacentRankModelIntegrand F ψ ν hself σ ℓ χ Ψ g h
Padic.AdjacentRankModelConverges F ψ ν hself σ ℓ χ Ψ g
Padic.adjacentRankModelIntegral  F ψ ν hself σ ℓ χ Ψ g
```

are transparent definitions. Each is the generic definition above with
`abv = normalizedAbsoluteValue F.canonicalTopologicalData`. Convergence
and the integral also use the inner measure
`η = generalLinearHaar F.Carrier r`. This is the shared Haar measure on
the actual inner `GL_(r+1)`, not `GL_r` or `GL_(r+2)`, and it gives the
integral subgroup `GL_(r+1)(O_F)` mass one. The test space, evaluation,
action and kernel are the generic ones at these instances. All the laws
above therefore apply to the specializations after unfolding. The
specializations assume no comparison between the intrinsic Fourier Haar
scaling of `ν` and the normalized p-adic absolute value.

## Scope

The module defines data and proves elementary algebraic laws. The
following analytic claims of Section 6.1 and later sections are not
asserted:

- convergence of the integral for arbitrary test tensors (the first claim
  of the source's Proposition) or for large positive twists;
- smoothness or standard-character equivariance of the function
  `g ↦ adjacentRankModelIntegral … Ψ g`;
- membership in, or spanning of, the induced Whittaker model `W(σ; ψ)`
  (the second claim of the Proposition);
- reversal from the lower family to the upper one, star transforms,
  determinant-shell expansions, functional equations, rational
  continuation and gamma or L factors.

These need separate statements and proofs.
