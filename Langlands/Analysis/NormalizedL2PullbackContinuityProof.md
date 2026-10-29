# Joint continuity of normalized L² pullback: proof

Authors: Worker 452 and Worker 997.

This module proves the theorem
`Langlands.NormalizedL2Pullback.locallyConstantScalingContinuity`, whose
type is exactly the published proposition
`Langlands.NormalizedL2Pullback.LocallyConstantScalingContinuity.{uX,uY,uZ}`
from `Langlands.Analysis.NormalizedL2PullbackContinuityStatement`, with
independent universe parameters `uX`, `uY` and `uZ` in that order. The
module imports only that statement module, which in turn imports the
published `Langlands.Analysis.NormalizedL2Pullback` and the Mathlib modules
used below. It adds no hypothesis and no axiom; the only axioms used are
Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

## Exact hypotheses and conclusion

The spaces `X : Type uX`, `Y : Type uY`, and `Z : Type uZ` have independent
universes. Both `X` and `Y` have a topology, a measurable structure,
`BorelSpace`, and `R1Space`; `Z` has an arbitrary topology. Let
`μ : Measure X` be `InnerRegularCompactLTTop` and let `ν : Measure Y`
be locally finite. The measurable equivalences `e : Z → X ≃ᵐ Y` and
scalars `c : Z → ℝ≥0` satisfy

```text
hc : ∀ z, c z ≠ 0,
hmap : ∀ z, μ.map (e z) = c z • ν.
```

Assume joint continuity of `(z, x) ↦ e z x` on `Z × X` and
`IsLocallyConstant c`. The conclusion is joint continuity, for the product
topology and the actual L² norm topologies, of

```lean
fun zf : Z × Lp ℂ 2 ν =>
  isometryEquiv (e zf.1) (c zf.1) (hc zf.1) (hmap zf.1) zf.2
```

with codomain `Lp ℂ 2 μ`. The operator is exactly the published
`Langlands.NormalizedL2Pullback.isometryEquiv`, on Mathlib's actual spaces
of almost-everywhere equivalence classes, with normalization
`normalization a = ((√a : ℝ) : ℂ)⁻¹`. The proof uses no continuity of the
inverse family, no group structure, no measure normalization and no local
compactness, and it makes no operator-norm continuity claim.

## Implemented proof

The proof has three private helper lemmas and the main theorem.

**Identity pullback with a fixed scalar.** For `a : ℝ≥0`, the private
lemma `map_refl_smul` proves `(a • ν).map (MeasurableEquiv.refl Y) = a • ν`
by rewriting the measurable identity equivalence as `id` and applying
`Measure.map_id`. For `a ≠ 0` this identity feeds the published
`isometryEquiv` with source measure `ν`, target measure `a • ν` and the
identity equivalence, giving an isometry
`J : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 (a • ν)` whose image of `f` is represented
almost everywhere by `normalization a • f`.

**Factorization through measure-preserving composition.** If
`μ.map e = a • ν`, then `e` is measure-preserving from `μ` to `a • ν`
(its measurability and this identity). The private lemma
`comp_normalized_identity` proves

```text
Lp.compMeasurePreserving e _ (J f) = isometryEquiv e a ha hmap f.
```

It applies `Lp.ext` and combines three almost-everywhere identities: the
representative formula `Lp.coeFn_compMeasurePreserving` for the left side,
the formula `coeFn_isometryEquiv` for `J f` pulled back along `e` by
`QuasiMeasurePreserving.ae_eq_comp`, and `coeFn_isometryEquiv` for the
right side. Both sides are thus represented `μ`-almost everywhere by
`x ↦ normalization a • f (e x)`.

**Scalar congruence.** The private lemma `isometryEquiv_scaling_congr`
shows that `isometryEquiv e c hc hmapc f = isometryEquiv e d hd hmapd f`
whenever `c = d`, by substituting the equality and closing by `rfl`
(proof irrelevance handles the hypotheses).

**Fixed-scalar continuity.** The private lemma `continuous_fixed_scaling`
treats a family `e : Z → X ≃ᵐ Y` with a single nonzero scalar `a` and
`hmap : ∀ z, μ.map (e z) = a • ν`, and a jointly continuous evaluation
map. Currying the continuous map `(z, x) ↦ e z x` with
`ContinuousMap.curry` gives a continuous `g : C(Z, C(X, Y))` for the
compact-open topology, and each `g z` is measure-preserving from `μ` to
`a • ν`. Mathlib's `Continuous.compMeasurePreservingLp`
(`Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving`,
with `p = 2` and the side condition `2 ≠ ∞` closed by `simp`), applied to
`zf ↦ J zf.2` (continuous since `J` is an isometry) and `zf ↦ g zf.1`,
gives continuity of `zf ↦ Lp.compMeasurePreserving (g zf.1) _ (J zf.2)`
on `Z × Lp ℂ 2 ν`. Its hypotheses are exactly the Borel, `R1Space`,
`InnerRegularCompactLTTop` and local finiteness assumptions on `μ` and
`a • ν`; the latter is found by instance search from local finiteness of
`ν`. By `comp_normalized_identity` this function equals
`zf ↦ isometryEquiv (e zf.1) a ha (hmap zf.1) zf.2`.

**Main theorem.** Continuity is proved pointwise through
`continuous_iff_continuousAt`. Fix `zf₀ : Z × Lp ℂ 2 ν` and let
`s = {zf | c zf.1 = c zf₀.1}`. It is open, as the preimage under the first
projection of the fiber of `c`, which is open by `IsLocallyConstant`, and
it contains `zf₀`. Take the subtype `s` as a new parameter space with the
family `q ↦ e q.val.1`. Its evaluation map is jointly continuous by
composing the original evaluation with continuous coordinate maps, and by
`hmap` and the defining equality of `s` its pushforward scalar is the fixed
`c zf₀.1`. The fixed-scalar lemma therefore gives continuity on
`s × Lp ℂ 2 ν`; composing with `q ↦ (q, q.val.2)` gives continuity on `s`
of `q ↦ isometryEquiv (e q.val.1) (c zf₀.1) … q.val.2`, which
`isometryEquiv_scaling_congr` identifies with the original function
restricted to `s`. Since `s` is open, its inclusion is an open embedding,
and `IsOpenEmbedding.continuousAt_iff` transfers continuity at the point
`⟨zf₀, rfl⟩` of `s` to continuity of the original function at `zf₀`. The
measure law with scalar `c zf₀.1` is only used on `s`.

## Provenance and scope

This is an internal analytic consequence of the published normalized
pullback construction and Mathlib's continuous measure-preserving
composition theorem; it does not transcribe a numbered literature result.
The proof uses those actual constructions and standard topological facts
and assumes no unproved analytic theorem.

The result is generic normalized-pullback continuity. Applying it to the
affine or mirabolic action still requires joint continuity of the actual
evaluation map of the relevant measurable equivalences and local constancy
of the pushforward scalar. Fourier and Plancherel theory, coefficient
completion, quotient transport, general semidirect induction and
block-induction irreducibility remain separate obligations.
