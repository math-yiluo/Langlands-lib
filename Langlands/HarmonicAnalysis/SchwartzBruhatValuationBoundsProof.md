# Valuation cutoffs and uniform bounds for scalar Schwartz–Bruhat functions: proof

Worker 231 authored the proof and this explanation, and also authored the
imported statement pair. Worker 656 specified the target interface and the
suggested route in the task. The imported Library results retain their
original authorship: the Schwartz–Bruhat space by Worker 20, and the
normalization definitions and proofs by Worker 27, with Worker 12 credited
on the normalization proof. No draft or implementation was reused in
Worker 231's original contribution. During integration, the Integrator
replaced its duplicate continuity helper with the existing proof extracted
from `Langlands.Representation.RankinSelberg.RootFiniteFunctionProof`
into `Langlands.LocalField.Normalization.Continuity`. Both consumers now
share that declaration, with the same statement and public name.

The module `Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof`
proves `Langlands.HarmonicAnalysis.schwartzBruhatValuationBounds`. Its type is
exactly the published proposition
`Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsStatement.{uF}`,
imported unchanged from
`Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsStatement`. The field
universe `uF` stays arbitrary.

## Statement and supplied topology

For every natural number `p` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData` and every
`Φ : HarmonicAnalysis.SchwartzBruhat F.Carrier`, formed with `T.topology`,
the theorem gives `L : ℤ`, `N : ℕ` and `C : ℝ` with `L ≤ N`, `0 < C`,
`‖Φ x‖ ≤ C` for every `x` (zero included), `Φ a = 0` for every unit `a` with
`T.ord a < L`, and `Φ a = Φ 0` for every unit `a` with `N ≤ T.ord a`.

The statement installs only `T.topology`, with `letI`. The proof introduces
`p`, the prime instance, `F`, `T` and `Φ`, and then installs the same
`T.topology` as a local instance for its own steps. It adds no hypothesis,
no other topology and no other instance. It does not assume `Φ 0 = 0`, a
support bound or a constancy threshold.

## Two helper lemmas

Both are stated in namespace `Langlands.PadicField.TopologicalData`, for an
arbitrary universe `u`, prime `p`, `F : PadicField.{u} p` and supplied `T`.
The continuity helper is imported from
`Langlands.LocalField.Normalization.Continuity`; the normalized-ball helper
is defined in this module.

- `continuous_normalizedAbs`: with `letI := T.topology`, the function
  `T.normalizedAbs : F.Carrier → ℝ` is continuous. The proof rewrites
  `T.topology` with the published
  `topology_eq_canonicalNormTopology`, which identifies it with the topology
  of `F.canonicalNormedField`. It then replaces `T.normalizedAbs` with
  `fun x => ‖x‖ ^ d`, where `d = Module.finrank (Padic p) F.Carrier`, by the
  published `normalizedAbs_eq_canonicalNorm_pow_degree`. That function is
  continuous by `continuous_norm.pow`.
- `exists_normalizedAbs_ball_subset`: if `s` is a neighbourhood of `0` for
  `T.topology`, there is `ε > 0` such that every `x` with
  `T.normalizedAbs x < ε` lies in `s`. The published basis
  `normalizedAbs_balls_basis` gives a basic set
  `{x | T.normalizedAbs (x - a) < ε}` with `ε > 0` that contains `0` and lies
  in `s`. Containing `0` means `T.normalizedAbs (-a) < ε`. For `x` with
  `T.normalizedAbs x < ε`, the published ultrametric inequality
  `normalizedAbs_add_le_max` applied to `x + (-a)` gives
  `T.normalizedAbs (x - a) < ε`, so `x` lies in the basic set.

## Main proof

Write `q` for the real number `T.residueCardinality`. The published
`residueCardinality_gt_one` gives `1 < q`.

1. **Uniform bound.** `Φ` is continuous with compact support
   (`SchwartzBruhat.continuous`, `SchwartzBruhat.hasCompactSupport`).
   Mathlib's `Continuous.bounded_above_of_compact_support` gives `C₀` with
   `‖Φ x‖ ≤ C₀` for every `x`. The proof takes `C = max C₀ 1`, which is
   positive and still bounds `‖Φ x‖`.
2. **Support bound.** `HasCompactSupport` means that `tsupport Φ` is compact.
   Since `T.normalizedAbs` is continuous (first helper),
   `IsCompact.exists_bound_of_continuousOn` gives `M` with
   `‖T.normalizedAbs x‖ ≤ M` on `tsupport Φ`. Since `1 < q`, Mathlib's
   `pow_unbounded_of_one_lt` gives `n : ℕ` with `M < q ^ n`. The proof takes
   `L = -n`.
3. **Constancy ball.** `Φ` is locally constant, so the fibre
   `{x | Φ x = Φ 0}` is open (`IsLocallyConstant.isOpen_fiber`). It contains
   `0`, so it is a neighbourhood of `0`. The second helper gives `ε > 0` such
   that `T.normalizedAbs x < ε` implies `Φ x = Φ 0`. Since `0 < q⁻¹ < 1`,
   Mathlib's `exists_pow_lt_of_lt_one` gives `N : ℕ` with `(q⁻¹) ^ N < ε`.

The order condition `-n ≤ N` holds because the left side is at most `0` and
the right side at least `0` (`omega`).

**Vanishing clause.** Let `a` be a unit with `T.ord a < -n`, and suppose
`Φ a ≠ 0`. Then `a` lies in the support, hence in `tsupport Φ`
(`subset_tsupport`), so `T.normalizedAbs a ≤ M`; the norm of this
nonnegative real is itself (`normalizedAbs_nonneg`). Because `a ≠ 0`, the
published `normalizedAbs_of_ne_zero` gives `T.normalizedAbs a = q ^ (-T.ord a)`.
From `T.ord a < -n` we get `n ≤ -T.ord a`, so `q ^ n ≤ q ^ (-T.ord a)` by
monotonicity of integer powers of `q ≥ 1` (`zpow_le_zpow_right₀`). Then
`M < q ^ n ≤ T.normalizedAbs a ≤ M`, a contradiction (`linarith`). Hence
`Φ a = 0`.

**Constancy clause.** Let `a` be a unit with `N ≤ T.ord a`. Again
`T.normalizedAbs a = q ^ (-T.ord a)`, and `-T.ord a ≤ -N` gives
`q ^ (-T.ord a) ≤ q ^ (-N) = (q⁻¹) ^ N < ε`. The constancy ball then gives
`Φ a = Φ 0`.

Both order clauses use only units, through `a.ne_zero`. The convention
`T.ord 0 = 0` is never used. The value at zero enters only as `Φ 0` and
through the uniform bound.

## Scope and provenance

This is a derived internal interface, not a numbered result of the cited
source. The statement Markdown cites H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, Amer. J. Math. **105** (1983),
printed p. 392 (one-based PDF p. 27), display (6) and the following
paragraphs (registered source `jpss-1983-rankin-selberg`). The source states
none of these facts as a separate result. The proof follows the standard
argument suggested in the statement Markdown and the task: compactness bounds
the normalized absolute value on the support, and local constancy at zero
gives a small normalized ball.

The proof uses the published Library results
`Langlands.PadicField.TopologicalData.topology_eq_canonicalNormTopology`,
`normalizedAbs_eq_canonicalNorm_pow_degree`, `normalizedAbs_balls_basis`,
`normalizedAbs_add_le_max`, `normalizedAbs_nonneg`,
`normalizedAbs_of_ne_zero` and `residueCardinality_gt_one` from
`Langlands.LocalField.Normalization.Proof`, together with the
`SchwartzBruhat` API from `Langlands.HarmonicAnalysis.Basic`. All of them are
imported by Lean name and remain unchanged. It makes no measure, Mellin
convergence, translation-recurrence or rational-continuation assertion.

The theorem compiles with no errors or warnings. The only axioms are
`propext`, `Classical.choice` and `Quot.sound`, and the level parameter is
`uF`. The environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
