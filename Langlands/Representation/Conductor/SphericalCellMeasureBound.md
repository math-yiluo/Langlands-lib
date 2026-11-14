# Exponential bounds for the masses of the Iwasawa cells

Author: Worker 5220. Internal helper module for the proof of
`Langlands.Conductor.SphericalCorankOneConvergenceStatement`; it introduces no
statement.

## Results

- `exists_finset_translate_cover`: for a compact open subgroup `K` of a topological
  group and any `g`, finitely many `y` satisfy: every `g k` (`k ∈ K`) equals
  `k' g y` for some `k' ∈ K` and some `y` of the finite set. The right cosets of the
  open subgroup `K ∩ g⁻¹ K g` cover the compact `K`.
- `isOpen_integralSubgroup'`, `isCompact_integralSubgroup'`: `GL_(n+1)(O)` is open
  and compact.
- `measure_rightTranslate_image`: a measure on `N_(n+1) \ GL_(n+1)(F)` that is
  preserved by every right translation gives a measurable set and its right
  translate the same mass.
- `exists_sphericalCell_measure_step`: for each exponent `δ` there is `c` with
  `μ(cell(λ + δ)) ≤ c μ(cell λ)` for every `λ`, where `cell λ` is the published
  `sphericalCell` (the image of `ϖ^λ GL_(n+1)(O)` in the quotient). The proof uses
  `sphericalCell_eq_image`, the cover for `g = ϖ^δ`, and right invariance.
- `exists_sphericalCell_measure_le`: there is `c ≥ 1` with
  `μ(cell λ) ≤ μ(cell 0) c^(∑ |λ_i|)` for every `λ`, by induction on `∑ |λ_i|`
  with the steps `δ = ± e_i`.

The hypotheses are a Borel measurable structure on the quotient and right
invariance of `μ`, both supplied by Jacquet's normalization
(`IsJacquetNormalization.borel`, `.measure.right_invariant`).

## Provenance

Elementary (internal); used to bound the cellwise integrals in the convergence
proof of JPSS 1983, §2.
