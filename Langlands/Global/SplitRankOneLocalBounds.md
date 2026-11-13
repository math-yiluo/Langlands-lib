# Local bounds for the binary form and its rational orbit points

Author: Worker 10.

This module collects norm bounds for the binary form
`ν(x) = ∑_{l ≤ m} x₀^(m-l) x₁^l w_l` over a normed field, in both the
ultrametric and the general case, and its compatibility with ring
homomorphisms. It also shows that for every nonzero rational `r`, the value
`ν(r)` is a nonzero multiple of a rational orbit point `ρ(q) e_j`.

## Provenance

This is internal infrastructure for the split rank-one height bound
(`SplitRankOneAdelic.md`); it does not formalize a literature statement. The
estimates are elementary.

## Results

Ring homomorphisms:

- `map_binaryForm` and `map_nu`: applying a ring homomorphism `f : K →+* L`
  coordinatewise commutes with the binary form. The coefficients `w_l` and the
  variables are mapped by `f`.

Norms, over a normed field `K` with the sup norm on `n → K` and `Fin 2 → K`:

- `norm_binaryForm_term_le`: if `‖w_l‖ ≤ B` for all `l ≤ m`, every term
  satisfies `‖(x₀^(m-l) x₁^l) • w_l‖ ≤ B ‖x‖^m`.
- `norm_nu_le_ultra`: for ultrametric `K` and `B ≥ 0`, `‖ν(x)‖ ≤ B ‖x‖^m`.
- `norm_nu_le`: in general, `‖ν(x)‖ ≤ (m+1) B ‖x‖^m`.
- `norm_mulVec_le_of_norm_le_one`: over an ultrametric `K`, a matrix whose
  entries all have norm at most `1` does not increase the sup norm.

Rational orbit points:

- **`CellData.exists_rational_orbit`** (for `F` infinite and
  `D : CellData ρ j i α`): for every nonzero `r : Fin 2 → F`, there are a
  rational point `q` of `G` and `c ≠ 0` in `F` with
  `ν(r) = c • ρ(q) e_j`. There are two cases.
  - If `r₀ ≠ 0`, take `q = xm(r₁ / r₀)` and `c = r₀^k`. This uses the
    dehomogenized lowering curve `xm(t) e_j = ν(1, t)`.
  - If `r₀ = 0`, then `r₁ ≠ 0`; take `q = xp(-1) xm(1)` and `c = r₁^k`. This
    uses `raising_mulVec_binaryForm`: `xp(-1) ν(1, 1) = ν(0, 1)`.
