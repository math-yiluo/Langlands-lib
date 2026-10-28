# Joint continuity of normalized L² pullback: statement

Authors: Worker 452 and Worker 872.

This module states the proposition
`Langlands.NormalizedL2Pullback.LocallyConstantScalingContinuity`,
with universe parameters `uX`, `uY` and `uZ` in that order. It supplies
a proposition definition (a `def` whose value is a `Prop`) and no proof
of that proposition. It imports the published module
`Langlands.Analysis.NormalizedL2Pullback`, Mathlib's
`Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving`
and `Mathlib.Topology.LocallyConstant.Basic`.

## Parameters and hypotheses

The spaces `X : Type uX`, `Y : Type uY` and `Z : Type uZ` have independent
universes. Both `X` and `Y` carry a topology, a measurable structure that
is the Borel σ-algebra of that topology (`BorelSpace`), and the separation
property `R1Space`. Any such Borel structure is allowed. The parameter
space `Z` carries an arbitrary topology and no measurable structure. Let

```text
μ : Measure X,   ν : Measure Y,
[μ.InnerRegularCompactLTTop],   [IsLocallyFiniteMeasure ν].
```

The first measure hypothesis is inner regularity of `μ` with respect to
compact sets, for sets of finite measure. The second is local finiteness
of the target measure `ν`. No local compactness, σ-finiteness, measure
normalization, Haar property or group structure is required.

The family `e : Z → (X ≃ᵐ Y)` consists of actual measurable equivalences.
The scalars `c : Z → ℝ≥0` are finite and nonnegative, with
`hc : ∀ z, c z ≠ 0`, and satisfy the pushforward identities

```text
hmap : ∀ z, μ.map (e z) = c z • ν.
```

Here `ℝ≥0` acts on measures by scalar multiplication. These laws are
hypotheses; the statement derives no measure law. The two remaining
hypotheses, stated as the premises of the final implication, are:

- joint continuity of the actual evaluation map
  `fun zx : Z × X => e zx.1 zx.2`, for the product topology on `Z × X`;
- `IsLocallyConstant c`: every preimage under `c` is open, equivalently
  every scalar fiber `{z | c z = c z₀}` is an open subset of `Z`.

No continuity of the inverse family `z ↦ (e z).symm`, no group action, no
extra scaling theorem and no affine specialization is assumed.

## Conclusion

The conclusion is continuity of

```lean
fun zf : Z × Lp ℂ 2 ν =>
  isometryEquiv (e zf.1) (c zf.1) (hc zf.1) (hmap zf.1) zf.2
```

from `Z × Lp ℂ 2 ν` to `Lp ℂ 2 μ`. The domain has the product of the
topology of `Z` and the L² norm topology; the codomain has the L² norm
topology. This is joint continuity in the parameter and the vector. It
implies continuity of every fixed-vector orbit `z ↦ isometryEquiv … f`,
but it asserts no continuity in the operator norm.

The operator is exactly the published
`Langlands.NormalizedL2Pullback.isometryEquiv`, applied with the input
measure `ν` and the output measure `μ`; it is not a new model of the L²
carrier. `Lp ℂ 2 ν` and `Lp ℂ 2 μ` are Mathlib's actual spaces of
almost-everywhere equivalence classes. By the published
`coeFn_isometryEquiv`, a representative of the image of `f` is, `μ`-almost
everywhere,

```text
x ↦ normalization (c z) • f (e z x),
normalization a = ((√a : ℝ) : ℂ)⁻¹.
```

Since `c z ≠ 0`, the normalization is the positive inverse square root of
the pushforward scalar. A representative formula is an almost-everywhere
identity, not a pointwise equality of chosen representatives.

## Provenance and suggested proof route

This is an internal analytic target. It is derived from the published
normalized pullback construction and Mathlib's continuous-composition
interface, and it does not transcribe a numbered literature theorem.
Mathlib's `Lp.compMeasurePreserving_continuous` and
`Continuous.compMeasurePreservingLp` state joint continuity of composition
of an `Lp` function with a continuous measure-preserving map, for
`1 ≤ p` and `p ≠ ∞`. They use the same Borel, `R1Space`,
`InnerRegularCompactLTTop` and `IsLocallyFiniteMeasure` hypotheses, and the
compact-open topology on `C(X, Y)`.

These lemmas suggest the following route; nothing in this module proves or
assumes it. Fix `z₀` and work on the open fiber `U = {z | c z = c z₀}`.
Replace `ν` by the fixed measure `c z₀ • ν`, which is again locally finite.
For `z ∈ U`, `hmap z` says that `e z` is measure-preserving from `μ` to
`c z₀ • ν`. Joint continuity of the evaluation makes `z ↦ e z` continuous
into `C(X, Y)` (by `ContinuousMap.curry`). The published normalized
pullback along the identity of `Y`, with scalar `c z₀`, is an isometry
from `Lp ℂ 2 ν` to `Lp ℂ 2 (c z₀ • ν)` with representative
`normalization (c z₀) • f`. Composing it with Mathlib's continuous
measure-preserving composition gives, on `U`, the required normalized
representative `normalization (c z) • f (e z x)`. Since local constancy
makes each fiber open, continuity at every point then follows from
continuity on these open sets. This paragraph describes a route only; it
is not a proved input of this statement.

## Scope

This statement alone proves no continuity, including this proposition
itself, whose proof is a separate obligation. It proves no affine or
mirabolic strong continuity, no Fourier or Plancherel theorem, no
affine or mirabolic irreducibility, no coefficient completion or quotient
transport, no general semidirect induction and no final block induction
irreducibility.
