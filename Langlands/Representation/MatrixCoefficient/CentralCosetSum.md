# Integrals over `G ⧸ Z(G)` as sums over cosets of an open subgroup

Author: Worker 4988.

## Statements

`G` is a topological group and `Z(G) = Subgroup.center G`. `q.out` is the representative
that Mathlib chooses for a class `q`.

* `exists_out_mk_eq_mul_center`, `exists_out_mk_eq_mul`: the chosen representative of the
  class of `g` is `g` times an element of the center, or of `J`, respectively.
* `isOpen_of_mul_mem`, `isOpen_of_mul_mem_left`: a set stable under right (respectively
  left) multiplication by an open subgroup is open.
* `setOf_out_mem_eq_image`, `isOpen_setOf_out_mem`: if `T ⊆ G` is stable under right
  multiplication by the center, then `{q | q.out ∈ T}` is the image of `T` in `G ⧸ Z(G)`.
  It is open when `T` is open.

In the rest of the file, `J` is an open subgroup of `G` that contains `Z(G)`.

* `centralImage J = {q | q.out ∈ J}`, the image of `J` in `G ⧸ Z(G)`.
  `mk_mem_centralImage_iff`: the class of `g` lies in it iff `g ∈ J`.
  `isOpen_centralImage`: it is open.
* `measurable_out`: if `Φ : G → M` satisfies `Φ (g * j) = Φ g` for `j ∈ J`, then
  `q ↦ Φ q.out` is measurable on `G ⧸ Z(G)` for any Borel measurable structure. No
  measurability of `Φ` is assumed.

Now `μ` is a Haar measure on `G ⧸ Z(G)` that is also right invariant.

* `centralImage_measure_ne_zero`: `μ (centralImage J) ≠ 0`.
* `lintegral_out_eq_mul_tsum`: if `Φ : G → ℝ≥0∞` is right `J`-invariant, then
  `∫⁻ q, Φ q.out ∂μ = μ (centralImage J) * ∑' α : G ⧸ J, Φ α.out`.
* `lintegral_out_eq_mul_tsum_inv`: if `Φ` is left `J`-invariant, then
  `∫⁻ q, Φ q.out ∂μ = μ (centralImage J) * ∑' α : G ⧸ J, Φ α.out⁻¹`.
* `tsum_out_eq_tsum_out_inv`: if moreover `μ (centralImage J) ≠ ∞` and `Φ` is invariant
  under `J` on both sides, then `∑' α, Φ α.out = ∑' α, Φ α.out⁻¹`.
* `lintegral_out_mul_eq`: if `Φ (g * z) = Φ g` for central `z`, then
  `∫⁻ q, Φ (q.out * h) ∂μ = ∫⁻ q, Φ q.out ∂μ` for every `h ∈ G`.

## Provenance

These are internal helpers for the proof of the Remark of Renard IV.3.2
(`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`).
That statement gives a Haar measure on `G ⧸ Z(G)` that is also right invariant. The proof
uses the open subgroup `J = K · Z(G)` for a compact open subgroup `K`. These lemmas turn the
`L²` norms of matrix coefficients into `ℓ²` norms on `G ⧸ J`. `tsum_out_eq_tsum_out_inv`
is the unimodularity fact that gives the tracial property in the proof. The facts are
standard; the statements and proofs are Worker 4988's. Mathlib proves inversion invariance of
Haar measure only for commutative groups, so the proof compares the partitions of
`G ⧸ Z(G)` into left and into right cosets of `J` instead.

## Lean proof

* Openness: `g ∈ T` has the open neighbourhood `g J ⊆ T` (`isOpenMap_mul_left`), or `J g`
  for left stability.
* `setOf_out_mem_eq_image`: `q = mk q.out`, and the representative of `mk g` is `g z` with
  `z` central (`QuotientGroup.mk_out_eq_mul`). The image of an open set is open
  (`QuotientGroup.isOpenMap_coe`).
* `measurable_out`: the preimage of any set under `q ↦ Φ q.out` is `{q | q.out ∈ Φ ⁻¹' s}`.
  `Φ ⁻¹' s` is right `J`-stable, hence open and stable under the center. So the preimage is
  open, hence measurable.
* `lintegral_out_eq_mul_tsum`: let `p q = mk_J q.out`. By invariance,
  `Φ q.out = Φ (p q).out`. The fiber `p ⁻¹' {α}` is the preimage of `centralImage J`
  under `q ↦ (mk α.out)⁻¹ * q` (`QuotientGroup.eq`). It is measurable and has measure
  `μ (centralImage J)` by left invariance (`measure_preimage_mul`). Then
  `Langlands.Analysis.lintegral_comp_eq_mul_tsum` from `Langlands/Analysis/FiberLIntegral.lean`
  applies.
* `lintegral_out_eq_mul_tsum_inv`: the same with `p q = mk_J q.out⁻¹`. Its fibers are the
  preimages of `centralImage J` under `q ↦ q * mk α.out`, so right invariance
  (`measure_preimage_mul_right`) gives their measure.
* `tsum_out_eq_tsum_out_inv`: compare the two formulas and cancel the finite nonzero factor
  (`ENNReal.mul_right_inj`).
* `lintegral_out_mul_eq`: `Φ (q.out * h) = Φ (q * mk h).out`, because the two arguments
  differ by a central factor. Then use `lintegral_mul_right_eq_self`.
