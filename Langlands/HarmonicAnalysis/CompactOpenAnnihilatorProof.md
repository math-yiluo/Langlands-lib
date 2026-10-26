# Compactness of compact-open annihilators: proof

The module `Langlands.HarmonicAnalysis.CompactOpenAnnihilatorProof` proves
`Langlands.HarmonicAnalysis.compactOpenAnnihilator.{u}`, whose type is exactly
[`Langlands.HarmonicAnalysis.CompactOpenAnnihilatorStatement.{u}`](CompactOpenAnnihilatorStatement.md).
The statement pair, [`Basic`](Basic.md) and the published
[`Hecke.TestFunction`](../Representation/Hecke/TestFunction.md) module are
imported unchanged.
The proof keeps the universe `u` and exactly the generic field, topology,
measure and character hypotheses of the statement, and it covers discrete
fields. It uses no sigma-finiteness, second countability, continuous
inversion, valuation, nondiscreteness, chosen conductor, or p-adic
assumption, and it does not use `ScalarFourierClosureStatement`.

Throughout, `A` denotes the annihilator
`{y : F | ∀ x : F, x ∈ H → ψ.complex (x * y) = 1}` of a compact open
additive subgroup `H`.

## Finite-measure open subgroups are compact

The theorem `isCompact_addSubgroup_of_measure_lt_top` works for any additive
topological group `G` that is Hausdorff and Borel. Its measure `μ` must be
left-invariant, regular and positive on nonempty open sets. If an additive
subgroup `A` is open and `μ A < ∞`, then `A` is compact.
The proof does not assume sigma-finiteness.

Since `A` is open and contains zero, `μ A` is nonzero, so `μ A / 2 < μ A`.
Inner regularity of the regular measure on the open set `A`
(`IsOpen.exists_lt_isCompact`) supplies a compact `K ⊆ A` with
`μ A / 2 < μ K`. Let `a ∈ A`. If `a` were not of the form `k₁ - k₂` with
`k₁, k₂ ∈ K`, the translate `{x | -a + x ∈ K}` would be disjoint from `K`.
That translate lies in `A`, because `x = a + (-a + x)`.
By left invariance it has measure `μ K`. Then `μ K + μ K ≤ μ A`, which
contradicts `μ A = μ A / 2 + μ A / 2 < μ K + μ K`. Hence `A` lies in the
image of `K ×ˢ K` under subtraction, a compact set. An open subgroup is
closed (`AddSubgroup.isClosed_of_isOpen`), so `A` is compact.

## The annihilator is an open subgroup

`exists_addSubgroup_annihilator` shows that, for any additive subgroup `H`,
the annihilator set is the carrier of an additive subgroup of `F`.
Zero belongs to it because `ψ.complex 0 = 1`. It is closed under addition by
distributivity and the character law. It is closed under negation because
`x * -a = -x * a` and `-x ∈ H`. No new data type is introduced: the main proof
only obtains this subgroup from an existential statement.

`annihilator_mem_nhds_zero` shows that the annihilator of a compact additive
subgroup `H` is a neighborhood of zero. Let `U` be the inverse image under `ψ`
of Mathlib's open right half arc `Circle.centeredArc (π / 2)`. It contains
`ψ 0 = 1` and is open by continuity of `ψ`. For each `x ∈ H`, continuity of
`(y, x) ↦ x * y` at `(0, x)` gives a product neighborhood mapped into `U`.
Compactness of `H` (`IsCompact.eventually_forall_of_forall_eventually`) then
gives a neighborhood of zero of parameters `y` with `x * y ∈ U` for every
`x ∈ H`. For such `y` and `x ∈ H`, every positive multiple `n • x` is in `H`,
and `ψ (n • x * y) = ψ (x * y) ^ n`. Therefore every positive power of
`ψ (x * y)` lies in the half arc, and
`Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two` gives
`ψ (x * y) = 1`. In the main proof, Mathlib's `AddSubgroup.isOpen_of_mem_nhds`
turns this neighborhood of zero into openness of the subgroup.

## Finite Haar measure from self-duality

`measure_annihilator_lt_top` proves `μ.measure A < ∞` under `IsSelfDual ψ μ`
for a compact open additive subgroup `H`. Let `f` be the published actual
characteristic function `Hecke.TestFunction.characteristic H.isClopen hH`.
It is a Schwartz–Bruhat function with values given by the indicator of `H`.
The first part of `IsSelfDual` for `f`, at Fourier parameter `0`, states
integrability of `x ↦ ψ.complex (x * 0) * fourierTransform ψ μ f x`.
Since `ψ.complex 0 = 1`, this is integrability of `fourierIntegral ψ μ f`.

For `y ∈ A`, the integrand `ψ.complex (x * y) * f x` equals the indicator of
`H` at every `x`: on `H` the character factor is one, and off `H` both sides
vanish. Hence `fourierIntegral ψ μ f y` is the real Haar mass
`μ.measure.real H`, viewed in `ℂ`. That mass is positive, because `H` is open
and nonempty and has finite measure by compactness. The transform therefore
has norm at least `μ.measure.real H` on `A`. Mathlib's non-quantitative Markov
inequality for integrable functions (`Integrable.measure_norm_ge_lt_top`)
shows that the set where the norm is at least this positive constant has
finite measure. Thus `A` has finite measure. The proof does not need the value
of the transform off `A`, and it uses no part of `IsSelfDual` other than this
integrability at parameter zero.

## Assembly

`compactOpenAnnihilator` introduces the quantified data. It obtains the
additive subgroup whose carrier is `A`, proves it open from
`annihilator_mem_nhds_zero` and of finite measure from
`measure_annihilator_lt_top`. It then applies
`isCompact_addSubgroup_of_measure_lt_top` to the bundled regular additive
Haar measure. Left invariance and positivity on open sets come from its
`IsAddHaarMeasure` field, and regularity comes from its `Regular` field.
Rewriting by the carrier equation gives compactness of the displayed
annihilator.

## Provenance

This is an internal derivation from the existing `Basic` interfaces, the
published Hecke characteristic test function and Mathlib's measure theory and
topology. No original-source theorem beyond those conventions is asserted.
The analytic route follows the outline in the task context: indicator
transform, integrability at zero, openness via the half-arc lemma, and the
inner-regularity difference-set argument. The implementation replaces the
outline's exact indicator formula with the Markov inequality. Worker 723 wrote
the proof. It does not copy or adapt code from Worker 86's unreviewed scalar
Fourier closure draft, although that draft's character local-constancy lemma
uses the same Mathlib half-arc lemma independently. Worker 86 supplied the
parent interface that this compactness result serves.
