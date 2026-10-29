# Integrability from geometric bounds on an exhaustion by boxes

Module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability`,
namespace `Langlands.RankinSelberg.TwoBlockConvergence`.

Author: Worker 886.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement` (JPSS 1983,
Section (4.6)). It supplies the measure-theoretic step: a pointwise geometric
bound on an exhaustion by boxes gives ordinary (Mathlib) integrability.

## Provenance

The content is internal to this proof. JPSS (source ID
`jpss-1983-rankin-selberg`), Section 4.6 (printed pages 410–411), reduce
convergence to a positive integral estimate. Here that estimate is replaced by
an elementary geometric-series bound over the boxes defined below.

## Abstract criterion (section `Abstract`)

`integrable_of_forall_exists_mem_box`: let `f : X → ℂ` be a.e. strongly
measurable. Let `box e` (`e ∈ ℕ`) be measurable sets with
`μ(box e) ≤ M Q^e` and `M < ∞`. Let `C, s ≥ 0` with `s Q < 1`, and suppose every
`x` lies in some `box e` with `‖f x‖ ≤ C s^e`. Then `f` is integrable.

Proof: pointwise `‖f x‖ₑ ≤ ∑_e C s^e 1_(box e)(x)`. The sets need not be
disjoint or nested. Integrate termwise (`lintegral_tsum`) to get
`∫⁻ ‖f‖ₑ ≤ ∑_e C M (s Q)^e = C M (1 - s Q)⁻¹ < ∞` (`ENNReal.tsum_geometric`).

## Boxes in a rectangular matrix space (section `Padic`)

`F` is a `p`-adic field with its canonical topological data `T`: integers
`O`, uniformizer `ϖ`, residue cardinality `q`.

- `box F j l e = {x : Matrix (Fin j) (Fin l) F | ∀ a b, ϖ^e x_(ab) ∈ O}`.
- `box_eq_pi`: the box is the product of the scalar sets `{z | ϖ^e z ∈ O}`.
  `measurableSet_box`: it is measurable, since `O` is open.
- `measure_preimage_uniformizer_pow_mul`: for an additive Haar measure `μ`,
  `μ{z | ϖ^e z ∈ O} = q^e μ(O)`. This follows from the published scalar
  scaling `HarmonicAnalysis.padicScalarHaarScaling`
  (`μ.map (a ·) = |a|⁻¹ μ`) with `a = ϖ^e`, using `|ϖ^e| = q^(-e)`
  (`uniformizerUnit_zpow_abs`).
- `rectangularMeasure_box`: for the published `rectangularMeasure μ j l` (the
  iterated product measure),
  `rectangularMeasure μ j l (box F j l e) = μ(O)^(j l) (q^(j l))^e`, computed by
  `Measure.pi_pi`.
