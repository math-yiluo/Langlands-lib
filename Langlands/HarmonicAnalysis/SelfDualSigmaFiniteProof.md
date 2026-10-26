# Sigma-finiteness of self-dual additive Haar measures

`Langlands.HarmonicAnalysis.selfDualSigmaFinite` proves
[`SelfDualSigmaFiniteStatement.{u}`](SelfDualSigmaFiniteStatement.md). It
uses exactly that statement's hypotheses and works in an arbitrary universe
`u`. The proof splits on whether the singleton `{0}` is open in `F`.

## Discrete case

`isFiniteMeasure_of_isSelfDual_of_isOpen_singleton_zero` uses only the
statement's hypotheses, plus the case assumption that `{0}` is open. Under
these hypotheses it shows that `μ.measure` is a finite measure.

When `{0}` is open, `F` carries the discrete topology. The indicator `f` of
`{0}` is then locally constant and has compact support, so it is a
`SchwartzBruhat F` test function. For every `y`, the integrand
`x ↦ ψ.complex (x * y) * f x` is the indicator of `{0}` with constant value
`1`, because `ψ.complex 0 = 1`. So the Fourier transform of `f` is the
constant `μ.measure.real {0}`.

`IsSelfDual ψ μ` includes the integrability clause of the second Fourier
integral. Applied to `f` at `y = 0`, that clause says this constant is
integrable. The open set `{0}` has positive measure. It is also compact, so
its measure is finite. The constant is therefore a nonzero complex number,
and Mathlib's `integrable_const_iff_isFiniteMeasure` gives
`IsFiniteMeasure μ.measure`. A finite measure is sigma-finite.

## Nondiscrete case

If `{0}` is not open, the punctured neighbourhood filter `𝓝[≠] 0` is
nontrivial. `sigmaCompactSpace_of_addHaar` then shows that `F` is a
sigma-compact space. It needs only a regular additive Haar measure. Neither
self-duality nor total disconnectedness is used. A locally finite measure on a
sigma-compact space is sigma-finite, and Mathlib infers this instance.

The scaling factor is Mathlib's `distribHaarChar F : Fˣ →* ℝ≥0`. The identity
`distribHaarChar_mul` gives `Δ g * μ s = μ (g • s)` for every unit `g` and set
`s`, where `Δ = distribHaarChar F`. The implemented argument has five steps.

1. Choose a compact neighbourhood `V` of `0`. Its measure is finite and
   nonzero. Because `0` is not isolated, `V` has an interior point `p ≠ 0`.
   Separate `0` from `p` by disjoint open sets `U ∋ 0` and `O ∋ p`. Then
   `V \ O` is still a neighbourhood of `0`. Since `interior V ∩ O` is a
   nonempty open set, it has positive measure, and this gives
   `μ (V \ O) < μ V`.
2. Continuity of multiplication and the tube lemma
   (`IsCompact.eventually_forall_of_forall_eventually`) give the following
   statement: for every `b` close enough to `0`, `b * v ∈ V \ O` for all
   `v ∈ V`. Since `0` is not isolated, we may pick such a `b` with `b ≠ 0` and
   `b ∈ V`. Let `u` be the unit `b`. Then `u • V ⊆ V \ O`, so
   `Δ u * μ V ≤ μ (V \ O) < μ V`, and therefore `Δ u < 1`.
3. The compact sets `S n = u ^ n • V` decrease. Their intersection is
   contained in `{0}`. Suppose `x ≠ 0` lies in every `S n`, and let `w` be
   the unit `x`. Then `((u ^ n)⁻¹ * w) • V ⊆ V * V`, and this gives
   `Δ w * μ V ≤ Δ u ^ n * μ (V * V)` for every `n`. The set `V * V` is
   compact, so its measure is finite. Since `Δ u < 1`, the right side tends
   to `0`. But `Δ w > 0` and `μ V ≠ 0`, which is a contradiction.
4. Fix `x ∈ F`. The preimage of `V` under `y ↦ x * y` is a neighbourhood of
   `0`, and hence a neighbourhood of `⋂ n, S n`. A decreasing family of
   compact sets eventually lies inside any neighbourhood of its intersection
   (`exists_subset_nhds_of_isCompact`). So `x * S n ⊆ V` for some `n`.
5. Since `b ∈ V`, the point `u ^ n • b` lies in `S n`, so
   `u ^ (n + 1) • x = x * u ^ n * b ∈ V`, that is,
   `x ∈ (u ^ (n + 1))⁻¹ • V`. So the compact sets `(u ^ n)⁻¹ • V` cover `F`,
   and `F` is sigma-compact.

The module also records the measure-free corollary
`sigmaCompactSpace_of_nhdsNE_neBot`. It equips `F` with its Borel structure
and applies `sigmaCompactSpace_of_addHaar` to Mathlib's `addHaarMeasure`. The
main theorem does not use it.

## Scope

None of the arguments assumes that inversion is continuous, that `F` is a
topological division ring, or that `F` is second-countable. The proof needs no
literature source: it combines the self-duality predicate from
[`Basic.md`](Basic.md) with standard properties of Haar measure on locally
compact fields.
