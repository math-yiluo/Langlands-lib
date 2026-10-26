# Finite-product preservation and reflection of MemLp

Author: Worker 629.

## Result and scope

The module proves the closed, published proposition
`Langlands.FiniteProductMemLpStatement.{uι, uX}` in
`Langlands.Analysis.FiniteProductLpStatement`. Its closing theorem is

```lean
Langlands.finiteProductMemLp.{uι, uX} :
  Langlands.FiniteProductMemLpStatement.{uι, uX}
```

There are no outer arguments or additional hypotheses. The two component
proofs are also available as closed theorems:

```lean
Langlands.finiteProductMemLpPreservation.{uι, uX} :
  Langlands.FiniteProductMemLpPreservationStatement.{uι, uX}

Langlands.finiteProductMemLpNonzeroIff.{uι, uX} :
  Langlands.FiniteProductMemLpNonzeroIffStatement.{uι, uX}
```

The index and factor-space universes are independent. The statements retain
an arbitrary finite nonempty index type, a dependent family of measurable
spaces, explicit sigma-finiteness of each supplied measure, the actual dependent
function space and its `Measure.pi`, and every real exponent `r > 0`.

For `F x = ∏ i, f i (x i)`, preservation asserts

```text
(∀ i, MemLp (f i) (ENNReal.ofReal r) (μ i)) →
  MemLp F (ENNReal.ofReal r) (Measure.pi μ).
```

It includes signed real functions and factors that are zero almost everywhere.
Reflection assumes each factor is almost everywhere strongly measurable and
is not almost everywhere equal to zero; under these hypotheses it proves

```text
MemLp F (ENNReal.ofReal r) (Measure.pi μ) ↔
  ∀ i, MemLp (f i) (ENNReal.ofReal r) (μ i).
```

The reflection implication assumes no integrability of the individual factors.
The nonzero assumption allows a factor to vanish on a set of positive measure.

## Implemented proof

All elementary helpers are private to this module. For a family of
nonnegative extended-real functions `g i`,
`aemeasurable_separated_prod` pulls each factor back along
`Measure.quasiMeasurePreserving_eval` and multiplies the resulting a.e.
measurable functions. The corresponding helper
`aestronglyMeasurable_separated_prod` does the same for real factors and a.e.
strong measurability. These maps only need to preserve null sets.

`lintegral_fin_separated_prod` proves the identity

```text
∫⁻ x, ∏ i, g i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, g i t ∂μ i
```

for indices `Fin n`, assuming a.e. measurability of the factors. At `n = 0`
the empty product space has mass one. The successor step uses the inverse of
`measurePreserving_piFinSuccAbove μ 0` to identify the product with the first
factor times the remaining dependent product, then applies
`lintegral_prod_mul` and the induction hypothesis. The helper
`lintegral_separated_prod` transfers this identity to an arbitrary finite index
type using `Fintype.equivFin` and `measurePreserving_piCongrLeft`. These are
nonnegative extended-real integrals; their identity does not assume finiteness.

`lintegral_power_separated_prod` applies this identity to
`g i t = ‖f i t‖ₑ ^ r`. Measurability follows from the factors' a.e. strong
measurability, `enorm`, and a measurable constant power. Multiplicativity of the
real norm (`nnnorm_prod`) and `ENNReal.prod_coe_rpow` identify the product
integrand with `‖F x‖ₑ ^ r`. Thus, writing

```text
A i = ∫⁻ t, ‖f i t‖ₑ ^ r ∂μ i,
```

we obtain `∫⁻ x, ‖F x‖ₑ ^ r ∂Measure.pi μ = ∏ i, A i`.

For positive `r`, `memLp_ofReal_iff_power_integral` specializes
`eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top` and
`ENNReal.toReal_ofReal`. Given a.e. strong measurability, it identifies `MemLp`
at exponent `ENNReal.ofReal r` with finiteness of this power integral.
Preservation follows from `ENNReal.prod_lt_top`; that lemma allows zero terms.

For reflection, `power_integral_ne_zero` shows that `A i ≠ 0` whenever
`f i` is not a.e. zero. Otherwise `lintegral_eq_zero_iff'` makes
`‖f i t‖ₑ ^ r` zero almost everywhere; positivity of `r` and
`ENNReal.rpow_eq_zero_iff_of_pos` imply `f i t = 0` almost everywhere.
Consequently every `A i` is nonzero, although it may initially be infinite.
If any one were infinite, `WithTop.prod_eq_top` would make their entire finite
product infinite. Finiteness of the product's power integral excludes this,
so each `A i` is finite and each factor is in `MemLp`. The converse is the
already proved preservation theorem. No coordinate slice or representative of
an `Lp` equivalence class is used.

## Provenance

This is an internal derivation from the published statement and Mathlib's
measure-theoretic APIs, rather than a quotation from representation theory.
The induction and reindexing organization adapts the finite-product integration
proofs in Mathlib's `MeasureTheory/Integral/Pi.lean`, authored by Xavier Roblot
and distributed under Apache 2.0. Here the argument uses Tonelli lintegrals in
place of Bochner integrals, retaining potentially infinite factor integrals.
The other APIs are in `MeasureTheory/Constructions/Pi.lean`,
`MeasureTheory/Measure/Prod.lean`, `MeasureTheory/Integral/Lebesgue/Basic.lean`,
`MeasureTheory/Function/LpSeminorm/Basic.lean`, and
`Analysis/SpecialFunctions/Pow/NNReal.lean` of the pinned Mathlib environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).

The proof imports the current statement module by Lean name and changes none
of its definitions. It establishes the finite-product `MemLp` result only;
no downstream representation-theoretic constructions are included.
