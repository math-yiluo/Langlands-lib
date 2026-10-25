# Finite-product preservation and reflection of MemLp

Author: Worker 450.

## Statements

This module defines the closed propositions
`Langlands.FiniteProductMemLpPreservationStatement`,
`Langlands.FiniteProductMemLpNonzeroIffStatement`, and their conjunction
`Langlands.FiniteProductMemLpStatement`. It supplies statements only. In
particular the equivalence and the integral identity described below are
remaining proof obligations.

Both component statements quantify over a finite nonempty index type
`ι : Type uι`, a dependent family `X : ι → Type uX`, an arbitrary supplied
measurable space on every `X i`, and supplied measures `μ i` with explicit
instances `∀ i, SigmaFinite (μ i)`. The index universe `uι` and space universe
`uX` are independent. The actual product space is the dependent function type
`(i : ι) → X i`, with its product measurable space and the actual finite
product measure `MeasureTheory.Measure.pi μ`. No topology, Borel condition,
probability normalization, finite total mass, or Haar structure is assumed.

For every family `f : ∀ i, X i → ℝ` and every real `r > 0`, put

```text
F x = ∏ i, f i (x i),     p = ENNReal.ofReal r.
```

The preservation statement asserts

```text
(∀ i, MemLp (f i) p (μ i)) → MemLp F p (Measure.pi μ).
```

It permits zero functions and factors that vanish almost everywhere.
Separate measurability premises are unnecessary here: each factor's
`MemLp` premise already supplies its almost-everywhere strong measurability.

The equivalence statement assumes
`∀ i, AEStronglyMeasurable (f i) (μ i)` and
`∀ i, ¬ (f i =ᵐ[μ i] (0 : X i → ℝ))`, and asserts

```text
MemLp F p (Measure.pi μ) ↔ ∀ i, MemLp (f i) p (μ i).
```

The nonzero premise means that no factor is almost everywhere equal to zero.
It does not require that a factor be nonzero almost everywhere, pointwise
nonzero, or nonnegative. In particular signed real functions are allowed.
The reflection implication starts with membership of the product alone;
integrability of any of the individual factors is not an additional premise.

Every real `r` is finite, and `0 < r` makes `p` positive and different from
infinity. Thus this interface includes `r = 2` and every `r = 2 + ε` for
`ε > 0`, as well as the valid stronger range of all positive real exponents.
It asserts no case at exponent zero or infinity.

## Internal derivation and positivity

These are internal measure-theoretic statements derived from the finite
product measure and Tonelli's theorem, rather than quotations of a
representation-theoretic theorem. A future proof can proceed as follows.
For each index define the nonnegative extended-real function and integral

```text
g i t = (ENNReal.ofReal |f i t|) ^ r,
A i   = ∫⁻ t, g i t ∂(μ i).
```

Almost-everywhere strong measurability pulls back along each coordinate
evaluation because it is quasi-measure-preserving for `Measure.pi μ`.
Finite multiplication then makes `F` almost everywhere strongly measurable.
The power of the absolute value of the separated product equals the
product of the individual powers. Iterating Tonelli gives the extended-real
identity

```text
∫⁻ x, (ENNReal.ofReal |F x|) ^ r ∂(Measure.pi μ) = ∏ i, A i.
```

This identity must be established even when some `A i` are infinite.
For positive finite `r`, `MemLp` is equivalent, given almost-everywhere
strong measurability, to finiteness of this power integral. A finite product
of finite `A i` is finite, which gives preservation, including zero factors.

For reflection, the zero-integral criterion and `r > 0` imply
`A i = 0 ↔ f i =ᵐ[μ i] 0`. The nonzero premises therefore give `0 < A i`
for every index, without asserting `A i < ∞`. If one `A i` were infinite,
its product with the remaining finitely many positive factors would be
infinite. Hence finiteness of `∏ i, A i` forces each `A i` to be finite.
This proves the required implication without assuming the other factors
integrable. No evaluation of an equivalence class on a coordinate slice is
used.

Positivity is essential. For example, on two copies of the real line with
Lebesgue measure, let the first factor be zero and the second be the constant
one function. The product belongs to every positive finite `L^r`, whereas
the second factor does not. The preservation statement retains this zero
case; the equivalence's nonzero premises exclude it.

## Pinned APIs and scope

The derivation uses Mathlib in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, pinned at Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Relevant existing APIs, read in
the pinned sources, are:

- `MeasureTheory.Measure.quasiMeasurePreserving_eval` and
  `MeasureTheory.Measure.pi.sigmaFinite` in
  `Mathlib/MeasureTheory/Constructions/Pi.lean`.
- `MeasureTheory.measurePreserving_piFinSuccAbove` and
  `MeasureTheory.measurePreserving_piCongrLeft` in the same file, for
  splitting the finite product and reindexing it without changing measures.
- `MeasureTheory.lintegral_prod` and
  `MeasureTheory.lintegral_prod_mul` in
  `Mathlib/MeasureTheory/Measure/Prod.lean`, for binary Tonelli and separated
  nonnegative products without finiteness assumptions on their integrals.
- `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top` in
  `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` and
  `MeasureTheory.lintegral_eq_zero_iff'` in
  `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`, for finiteness and
  positivity.

The explicit sigma-finiteness of every factor supplies the hypotheses
for the finite product construction and its coordinate maps and implies
sigma-finiteness, hence s-finiteness, of the product measures needed in the
Tonelli induction. It does not assert that the measures have finite total
mass. Coordinate evaluations need only preserve null sets; they are not
assumed measure-preserving.

Mathlib's `MeasureTheory.Integrable.fintype_prod_dep` in
`Mathlib/MeasureTheory/Integral/Pi.lean` already gives dependent finite-product
preservation at the level of integrable functions. Its
`MeasureTheory.integral_fintype_prod_eq_prod` is a Bochner-integral formula;
it cannot alone justify reflection when the individual power integrals
have not been shown finite. The extended-real Tonelli identity above is
the necessary route in that direction. Searches of the current Library,
pinned Mathlib, and current tasks found no equivalent ready finite-product
`MemLp` reflection target.

The only imports of this statement pair are the finite product measure
construction and basic `Lp` seminorm API. Its intended consumers include
the coefficient-norm product steps of
`Langlands/Representation/Classification/BlockTensorAnalyticStatement`.
It assumes none of that module's analytic obligations and supplies no
group quotient, central character, tensor representation, smooth-dual
decomposition, classification, or induction result. Those constructions
and their measure hypotheses remain obligations of the consumer.
