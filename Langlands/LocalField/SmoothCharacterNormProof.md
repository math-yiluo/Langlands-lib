# Proof of the real norm decomposition of a smooth scalar character

Author: Worker 723. The helper arguments adapt published Library proofs by
Worker 23 and Worker 225; see "Attribution and independence" below.

The theorem
`Langlands.PadicField.TopologicalData.smoothCharacterNormDecomposition F T`
proves the published proposition
`Langlands.PadicField.TopologicalData.SmoothCharacterNormDecomposition F T`
from `Langlands.LocalField.SmoothCharacterNormStatement`. It holds for every
prime `p`, every field `F : PadicField.{uF} p` in an arbitrary universe `uF`,
and every supplied `T : F.TopologicalData`. Its binders are those of the
statement: `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.

So for every `ω : F.Carrierˣ →* ℂˣ` whose kernel is open in `F.Carrierˣ` for
the topology of units induced by `T.topology`, there is exactly one real `c`
with

```text
‖(ω a : ℂ)‖ = T.normalizedAbs (a : F.Carrier) ^ c   for all a : F.Carrierˣ,
```

where the right side is `Real.rpow`. The exponent constructed is
`c = -Real.logb q ‖ω ϖ‖`. Here `q = T.residueCardinality` and
`ϖ = LocalFactor.PadicAbelian.uniformizerUnit T` is the specified uniformizer
`T.uniformizer`, viewed as a unit. No continuity of `ω` for the topology of
`ℂˣ` is assumed; only the open-kernel hypothesis is used. The statement pair
and every pair it imports are unchanged.

## Helper results

The module proves four helper theorems in the namespace
`Langlands.PadicField.TopologicalData`, for any field `F` and data `T`.

### Norm one is valuation one

`normalizedAbs_eq_one_iff_valuation_eq_one T x` states, for every field element
`x`, that `T.normalizedAbs x = 1` if and only if
`ValuativeRel.valuation F.Carrier x = 1` for the valuative relation carried by
`T`. At `x = 0` both sides are false. For `x ≠ 0` the published
`normalizedAbs_le_iff_of_ne_zero` compares `x` with `1` in both directions.
Its results are inequalities of `T.discreteValuation`, whose value at `x` is
the image of `ValuativeRel.valuation F.Carrier x` under the order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`. Antisymmetry and
injectivity of that isomorphism give the equivalence.

### The norm-one units are compact

`isCompact_normalizedAbs_eq_one_units T` states that, with `T.topology`
installed, the set `{a : F.Carrierˣ | T.normalizedAbs a = 1}` is compact in
the topology of units.

Let `S` be the set of field elements of valuation exactly `1`. Mathlib's
`Valuation.isClosed_sphere` shows that `S` is closed. `S` is contained in the
closed unit ball, which is compact by
`IsNonarchimedeanLocalField.isCompact_closedBall`, so `S` is compact. By the
first helper, the norm-one units are exactly the preimage of `S` under
`Units.val`. That map is an embedding (`Units.isEmbedding_val₀`; the field is
a topological division ring by Mathlib's local-field instance). Every point of
`S` is nonzero and so is the value of a unit. Hence the preimage is compact by
`IsInducing.isCompact_preimage'`.

### A smooth character has norm one on norm-one units

`norm_eq_one_of_normalizedAbs_eq_one T ω hω hu` states that if `ω` has open
kernel and `T.normalizedAbs u = 1`, then `‖ω u‖ = 1`.

The function `a ↦ T.normalizedAbs a` is a monoid homomorphism
`F.Carrierˣ →* ℝ`, by `normalizedAbs_one` and `normalizedAbs_mul`. Let `K` be
its kernel, the subgroup of norm-one units. `K` is a compact space by the
previous helper. The subgroup `U = ω.ker.subgroupOf K` is open in `K`
(`Subgroup.subgroupOf_isOpen`), so `K ⧸ U` is finite
(`Subgroup.quotient_finite_of_isOpen`). Hence `u ^ U.index ∈ U`
(`Subgroup.pow_index_mem`), so `ω u ^ U.index = 1` and
`‖ω u‖ ^ U.index = 1`. The index is nonzero, and a nonnegative real whose
nonzero power is one equals one (`pow_eq_one_iff_of_nonneg`).

### Reduction to the uniformizer

`norm_eq_norm_uniformizer_zpow_ord T ω hω a` states that
`‖ω a‖ = ‖ω ϖ‖ ^ T.ord a` (an integer power) for every unit `a`.

Put `k = T.ord a` and `u = a * ϖ ^ (-k)`. By `normalizedAbs_mul`,
`normalizedAbs_of_ne_zero` and the published `uniformizerUnit_zpow_abs`,
`T.normalizedAbs u = q ^ (-k) * q ^ k = 1`, using `q ≠ 0` from
`residueCardinality_gt_one`. Since `a = u * ϖ ^ k`, multiplicativity of `ω`
and of the complex norm, together with the previous helper, give
`‖ω a‖ = ‖ω ϖ‖ ^ k`.

## The main theorem

Let `q = T.residueCardinality`, so `1 < q` as a real number by
`residueCardinality_gt_one`. Let `r = ‖ω ϖ‖`, which is positive because `ω ϖ`
is a unit of `ℂ`.

Existence. For a unit `a` with `k = T.ord a`, `T.normalizedAbs a = q ^ (-k)`
by `normalizedAbs_of_ne_zero`. Rewriting this integer power as a real power
(`Real.rpow_intCast`) and using `Real.rpow_mul` (valid since `q ≥ 0`) gives

```text
T.normalizedAbs a ^ (-logb q r) = q ^ ((-k) * (-logb q r))
                                = (q ^ logb q r) ^ k = r ^ k.
```

Here `q ^ logb q r = r` by `Real.rpow_logb`, which uses `0 < q`, `q ≠ 1` and
`0 < r`. By the reduction helper, `r ^ k = ‖ω a‖`.

Uniqueness. Let `c` satisfy the identity for every unit. By
`uniformizerUnit_zpow_abs` with exponent `1`, `T.normalizedAbs ϖ = q⁻¹`.
Evaluating both identities at `ϖ` gives `q⁻¹ ^ c = q⁻¹ ^ (-logb q r)`. Taking
`Real.log` and applying `Real.log_rpow` (since `0 < q⁻¹`) yields
`c * log q⁻¹ = (-logb q r) * log q⁻¹`. Since `0 < q⁻¹ < 1`, `log q⁻¹ ≠ 0`
(`Real.log_ne_zero_of_pos_of_ne_one`), so `c = -logb q r`.

## Attribution and independence

The three topological and character-theoretic helpers adapt published
Library proofs. Two of them follow the arguments of Worker 23:
`norm_eq_one_of_isOpen_ker` and `norm_eq_zpow_ord_of_isOpen_ker` in
[RealPartExistence](../Representation/Exponents/RealPartExistence.md), and
`normalizedAbs_eq_one_iff_discreteValuation` in
[NormalizedCharacter](../Group/GL/NormalizedCharacter.md). The compactness
proof follows Worker 225's `CuspidalSupport.isCompact_ker_normalizedAbsUnits` in
[DeterminantUnitCentralCompactnessProof](../Representation/CuspidalSupport/DeterminantUnitCentralCompactnessProof.md).
The final exponent calculation follows Worker 23's
`norm_eq_normalizedAbs_rpow_of_isOpen_ker`.

These arguments are reimplemented here rather than imported. The published
originals live in modules that also import general linear group modules
(`NormalizedCharacter`) or representation-theoretic modules (the other two).
This module instead imports only the following:

- the target statement `Langlands.LocalField.SmoothCharacterNormStatement`;
- `Langlands.LocalField.Normalization.Proof`, the scalar normalization laws,
  whose project imports are only the normalization statement, the normalization
  definitions and `Langlands.LocalField.Definitions`;
- `Langlands.LocalField.Uniformizer`, the uniformizer unit, which imports only
  the normalization definitions;
- Mathlib.

The local subgroup `K` is built from `T.normalizedAbs` directly, not from
`T.normalizedAbsUnits`. Consequently, no proof input depends on a
classification, square-integrability, exhaustion or representation-theoretic
result. In particular, nothing here depends on the tasks excluded by the task
contract.

## Provenance and scope

This is an internal scalar local-field lemma, as the statement's Markdown
explains. Auel (2004), Definition 4.7 and Lemma 4.15, motivates it but does not
state or prove it. The proof is the standard argument: a compact group's open
subgroup has finite index, and a character is decomposed through the
uniformizer.

The checked theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. It constructs no invariant positive form and proves no
downstream analytic or representation-theoretic assertion.
