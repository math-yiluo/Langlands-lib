# Integral form of the open-cell exchange

Module `Langlands.Representation.RankinSelberg.RankOneExtensionUnfoldingIntegral`.

This helper module turns the measure identity `map_cellExchange` of
[RankOneExtensionUnfoldingMeasure](RankOneExtensionUnfoldingMeasure.md) into an identity
of Bochner integrals. It is used to unfold the zeta integral of the lower induced
representation of `GL_(1+(t+1))` in the rank-one extension step. It contains no
statement about representations.

## Provenance

In Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105
(1983), Lemma 5.5 (printed pp. 424–426), the integral over the lower parabolic cell is
unfolded by moving the unipotent variable `u(y)` across the lower block
`B(m, x, a) = [m, 0; x, a]`, as a one-line change of variables. This module states that
change of variables for a function `Ψ(q, z)` of a coset `q ∈ H \ GL_(t+1)` and a group
element `z ∈ GL_(1+(t+1))`. The function `Ψ` must satisfy
`Ψ(q, B(r, 0, 1) z) = Ψ(q r, z)`. The coordinates, the order of the factors and the
scaling weight were chosen for this formalization; they are not quoted from the paper.

## Contents

Cells (`section Cells`), for any field `K`:

- `lowerScalarUnit h` is the entry of `h ∈ B⁻_1 = lowerTriangularSubgroup 1 K` as a unit
  of `K`; `lowerScalarUnit_val` and `lowerScalarUnit_mul` give its value and
  multiplicativity.
- `rankOneExtensionLowerBlock_one_zero_one`: `B(1, 0, 1) = 1`.
- `rankOneExtensionLowerBlock_one_inv`: `B(1, x, a)⁻¹ = B(1, -a⁻¹ x, a⁻¹)`.
- `rankOneExtensionUpperCell_inv`: `u(y)⁻¹ = u(-y)`.
- `rankOneExtensionLowerCell x h` is `B(1, x, h) = [I, 0; x, h]`. Here `x` is a
  `1 × (t+1)` row matrix and `h ∈ B⁻_1`.
- `rankOneExtensionUpperCell_mul_lowerCell`: if `s = 1 + x · y ≠ 0`, then

  `u(y) B(1, x, h) = B(r, 0, 1) B(1, x, h') u(h' y)`,  with `r = I + y x`, `h' = h s⁻¹`.

  Here `r` is `rankOneExtensionCellShear` and `s⁻¹` is `rankOneExtensionCellScalarInv`.

Topology (`section Topology`), for a topological division ring `K`:

- `continuous_rankOneExtensionUpperCell`: `y ↦ u(y)` is continuous into
  `GL_(1+(t+1))(K)`.
- `continuous_rankOneExtensionLowerCell`: `(x, h) ↦ B(1, x, h)` is jointly continuous.

Both are checked through `Units.continuous_iff`, using the explicit inverses above.

Reordering (`section Reorder`):

- `cellReorder` is the measurable equivalence
  `((q, (x, h)), y) ↦ ((x, y), (q, h))`.
- `measurePreserving_cellReorder`: it sends `(μQ × (dx × ρ)) × dy` to
  `(dx × dy) × (μQ × ρ)` for s-finite measures.

Integrals (`section Integral`), for a second-countable topological field `K` with Borel
σ-algebras:

- `measurable_lowerCell_mul_upperCell`: `((x, y), (q, h)) ↦ (q, B(1, x, h) u(y))` is
  measurable.
- `integral_cellExchange`. Hypotheses:
  - finiteness: the measure `dx` on the `1 × (t+1)` row matrices, `μQ` and `ρ` are
    s-finite (`SFinite dx`, `SFinite μQ`, `SFinite ρ`), and `ν` on `K` is σ-finite
    (`SigmaFinite ν`). The other hypotheses below do not imply these. For example, for
    `K = ℝ`, counting measure on `B⁻_1 ≅ ℝ^×` is right-invariant but not s-finite;
  - `ν` has no atoms (`NullSingletonClass ν`); `y` is integrated against the row
    measure `ν^(t+1)`;
  - `μQ` on `H \ GL_(t+1)` is invariant under every right translation;
  - `ρ` on `B⁻_1` is right-invariant;
  - `χ : K →*₀ ℝ≥0` is measurable and `x ↦ a x` sends `ν` to `χ(a)⁻¹ • ν` for `a ≠ 0`;
  - `Ψ` is strongly measurable with `Ψ(q, B(r, 0, 1) z) = Ψ(q r, z)`.

  Conclusion, on `(dx × ν^(t+1)) × (μQ × ρ)`: the function
  `Ψ(q, u(y) B(1, x, h))` is integrable if and only if
  `χ(h)^(-(t+1)) • Ψ(q, B(1, x, h) u(y))` is integrable, and the two integrals are equal.
  Here `χ(h)` means `χ` applied to `lowerScalarEntry h`.
- `integral_cellExchange_reorder`: under the same hypotheses, including the four
  finiteness assumptions, the same statement on `(μQ × (dx × ρ)) × ν^(t+1)`, the order in
  which the lower-block disintegration `(μQ × (dx × ρ))` is followed by the upper-cell
  variable `y`.

## Proof method

Off the null set `{s = 0}` (`prod_cellScalar_eq_zero`), the exchange identity and the
compatibility of `Ψ` rewrite `Ψ(q, u(y) B(1, x, h))` as `G ∘ T`. Here
`G((x, y), (q, h)) = Ψ(q, B(1, x, h) u(y))` and `T` is `rankOneExtensionCellExchange` with
row `x ↦ x 0`. The measure identity `map_cellExchange` identifies `T`'s image measure
with the same measure with density `χ(h)^(-(t+1))`. The scaling hypothesis it needs comes
from `productMeasure_map_const_smul`. The conclusion then follows from
`integrable_map_measure`, `integral_map`, `integrable_withDensity_iff_integrable_smul` and
`integral_withDensity_eq_integral_smul`. The reordered form transports both statements
along the measure-preserving equivalence `cellReorder`
(`MeasurePreserving.integrable_comp_emb`, `MeasurePreserving.integral_comp'`).

The finiteness assumptions enter as follows. `productMeasure_map_const_smul` and the null
set `prod_cellScalar_eq_zero` need `ν` σ-finite; the latter also needs `dx` and
`μQ × ρ` s-finite. `map_cellExchange` needs `ν^(t+1)`, `μQ` and `ρ` s-finite, and
`measurePreserving_cellReorder` needs all four factors s-finite.

Measurability of `G` uses that `GL_(1+(t+1))(K)` is second countable
(`secondCountable_generalLinear`), so multiplication is jointly measurable, together with
the continuity lemmas above.

The upper-cell inverse and continuity laws listed above are reused from [RankOneExtensionCellTopology](RankOneExtensionCellTopology.md).
