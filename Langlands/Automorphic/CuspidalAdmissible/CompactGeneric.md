# Local averages on a topological group

Module: `Langlands.Automorphic.CuspidalAdmissible.CompactGeneric`. Provenance: internal; these
are standard measure-theoretic facts about averaging over a small neighbourhood, used for the
compact part of the joint admissibility proof.

Throughout `G` is a Hausdorff topological group with Borel structure and `ν` a measure on `G`
that is finite on compact sets.

- `enorm_sq_le_two_mul a b`: `‖a‖² ≤ 2‖b‖² + 2‖a - b‖²` in a seminormed group (extended norms).
- `avgMeasure ν U = (ν U)⁻¹ • ν|_U`; `isProbabilityMeasure_avgMeasure` when `0 < ν U < ∞`.
- `average ν U φ g = ∫ φ(g u) d(avgMeasure ν U)(u)`, the average of `φ` over the right
  translates `g u`, `u ∈ U`.
- `integrable_translate_avgMeasure`: for compact `U` with `ν U ≠ 0` and continuous `φ`,
  `u ↦ φ(g u)` is integrable for the averaging measure; hence `average_add` (additivity in
  `φ`) and `average_smul` (homogeneity, no hypothesis).
- `enorm_sub_average_sq_le` (Jensen): `|φ(g) - Aφ(g)|² ≤ ∫ |φ(g) - φ(g u)|² d(avgMeasure)(u)`;
  `enorm_average_sub_sq_le`: `|Aφ(g') - Aφ(g)|² ≤ ∫ |φ(g' u) - φ(g u)|² d(avgMeasure)(u)`.
  Both write the difference as one integral, use `‖∫ f‖ ≤ ∫ ‖f‖` and `sq_lintegral_le`.
- `lintegral_sub_average_le` (smoothing error): if `∫_Kc |φ - φ(· u)|² dν ≤ a` for every
  `u ∈ U`, then `∫_Kc |φ - Aφ|² dν ≤ a` (Jensen pointwise, Tonelli
  `lintegral_lintegral_swap` with joint continuity, averaging measure of mass one). Needs
  second countability and s-finiteness.
- `exists_finite_net`: a compact set `Kc` is covered by finitely many translates `p V`
  (`p ∈ Kc`) of a neighbourhood `V` of `1`.
- `setLIntegral_right_translates_le`: the right-invariant analogue of
  `setLIntegral_translates_le` (module `CuspIntegral`): for a right-invariant s-finite `ν`,
  continuous `φ_k` and a continuous curve `u` with `R u(σ) ⊆ t` for `σ ∈ [0, 1]`,
  `∫_R ∫_0^1 ∑_k |φ_k(g u(σ))|² dσ dν(g) ≤ ∑_k ∫_t |φ_k|² dν`.
