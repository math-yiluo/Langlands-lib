# Proof that unnormalized `Φ⁻` transfers covariant pairings

Author: Worker 806.

This module proves `Langlands.Derivative.Mirabolic.phiMinusPairingTransfer`, of type
`PhiMinusPairingTransferStatement.{uF, uV, uW} F T m`, for every p-adic field `F`,
topological data `T` and `m : ℕ`.

## Route

The source (Jacquet, Piatetski-Shapiro and Shalika 1983, §1.4, Proposition, printed
p.380, proof from p.381) treats representations induced from `P_(r-1)U_r` and uses
Frobenius reciprocity. The Lean proof does not use induced models. It integrates the
pairing over the radical directly, which is the formula recorded in the statement's
Markdown.

Notation: `P = mirabolic (m + 1) F`, `u(c)` is the radical element with coordinates
`c ∈ F^(m+1)` (`radicalElement c`), `c_last` is the last coordinate of `c`,
`levi g` embeds `g ∈ GL_(m+1)(F)` in `P`, `ε = levi (-1)`, `|·|` is
`normalizedAbsoluteValue T`, and `dc` is the additive Haar measure `Measure.addHaar` on
`F^(m+1)`. The given form `β` satisfies
`β (ξ g v) (ξ' g w) = |det g|^(-s) β v w`. Radical elements have determinant one, so
`β` is invariant under the radical.

### 1. The radical coefficients

For `v : V` and `w : W`, the coefficient `c ↦ β (ξ (u c) v) w` has two properties.

- **It is locally constant** (`exists_latticeBox_fixes`). Smoothness of `ξ` gives a
  lattice box `(π^(-l) O)^(m+1)` whose radical elements fix `v`, so the coefficient is
  invariant under translation by the box. It is therefore continuous
  (`continuous_of_forall_add_eq`).
- **It vanishes outside a lattice box** (`exists_coefficient_support`). This step
  uses the hypothesis that the vectors `ξ (u d) x − x` span `V`. The vectors `v`
  whose coefficient against `w` vanishes outside some box form a submodule, so it
  suffices to treat `v = ξ (u d) x − x`.
  - `exists_open_subgroup_coefficient`: there is an open subgroup `H` of
    `GL_(m+1)(F)` such that `levi H` fixes `x` and `w` and `|det| = 1` on `H`. By
    `levi_mul_radicalElement` and covariance, the coefficient of `x` is invariant
    under `c ↦ k c` for `k ∈ H`.
  - `exists_mulVec_eq_add`: for `c` outside a large box, choose a coordinate `j`
    with `c_j` large, let `r = c_j⁻¹ e_j` (small), and put `k = 1 + d r^T`. Then
    `k c = c + d`, and `k ∈ H` once `r` is small enough. Hence the coefficient of
    `x` at `c + d` equals its value at `c`. That is,
    `β (ξ (u c) (ξ (u d) x − x)) w = 0` for `c` outside the box.

### 2. The integral and its descent

`transferIntegral μ ψ ξ β v w = ∫ ψ(−c_last) β (ξ (u c) v) w dc`. Its integrand is
continuous with compact support, so it is integrable
(`integrable_transferIntegrand`), and the integral is bilinear (`transferForm`). Put
`B v w = transferIntegral (v, ξ' ε w)`.

- `transferIntegral_radical_left`: translation invariance of Haar measure gives
  `B (ξ (u d) v) w = ψ(d_last) B v w`.
- `transferIntegral_radical_right` and `levi_neg_one_mul_radicalElement`:
  `ε u(d) = u(−d) ε`. Radical invariance of `β` turns translating `w` by `u(−d)` into
  translating `v` by `u(d)`, so `B v (ξ' (u d) w) = ψ(d_last) B v w`.

The radical acts on the `Φ⁻` quotient through `θ_ψ(u(d)) = ψ(d_last)`
(`theta_radicalElement`), so `B` descends to the coinvariants of both factors by
two applications of `Jacquet.Localization.lift`. This gives the form `B₄` on the
underlying spaces of `Φ⁻ ξ` and `Φ⁻ ξ'`.

### 3. Covariance

`transferIntegral_levi` is a change of variables. For `g ∈ GL_(m+1)(F)`,
`u(c) levi g = levi g u(g⁻¹ c)` (`levi_mul_radicalElement`). The Library scaling law
`haarMeasure_map_matrix`, applied with `padicScalarHaarScaling`, gives
`μ.map (c ↦ k c) = |det k|⁻¹ μ`. Together they give

`I (ξ (levi g) v) (ξ' (levi g) w) = |det g|^(-s) · |det g| · ∫ ψ(−(g c)_last) β (ξ (u c) v) w dc`.

For `h` in `mirabolic m F`, the action of `h` on `Φ⁻` is `successor h = levi h`.
`ε` commutes with `levi h` (`levi_neg_one_commute`), and `(h c)_last = c_last`
(`mulVec_last`). So `B₄` is covariant with weight `|det h|^(-s) |det h|`, which
equals `|det h|^(-(s - 1))` by `determinantWeight_one_sub`.

### 4. Nonvanishing

Pick `v₀`, `w₀` with `β v₀ w₀ ≠ 0`. The coefficient `f(c) = β (ξ (u c) v₀) w₀` is
locally constant, vanishes outside a box, and has `f(0) ≠ 0`.

`exists_integral_character_ne_zero` then gives `y ≠ 0` with
`∫ ψ(−(y ⬝ c)) f(c) dc ≠ 0`. Its proof does not use Fourier inversion. Suppose
instead that all these integrals vanish for `y ≠ 0`.

- For `y` in a small box (level `n(ψ) − N`, where `f` vanishes outside the `N`-box),
  the integral equals `∫ f`. So `∫ f = 0` as well, and all twisted integrals vanish.
- Sum the twisted integrals over a finite set of representatives `y` of a quotient
  of boxes `A`-box / `B`-box. Pointwise in `c`, the character sum is
  `|Q| · f(0)` on a small box (level `C = n(ψ) − A`, where `f` is constant). Off
  that box it is `0`, by `sum_out_eq_zero` and
  `mem_latticeBox_of_forall_character_eq_one`.
- The integral of the sum is therefore `|Q| · f(0) · μ(C-box) ≠ 0`, because open
  sets have positive Haar measure and compact sets have finite measure. This
  contradicts the vanishing.

`EqualRankFrobenius.exists_lastRow_eq` gives `g ∈ GL_(m+1)(F)` with last row `y`, so
`(g c)_last = y ⬝ c`. Put `w₁ = ξ' ε⁻¹ w₀`. By step 3,
`B (ξ (levi g) v₀) (ξ' (levi g) w₁)` is `|det g|^(-s) |det g|` times that nonzero
integral. Both factors are nonzero, so `B ≠ 0` and hence `B₄ ≠ 0`.

## Auxiliary declarations

- Group identities: `rep_radicalElement_mul`, `rep_radicalElement_zero`,
  `levi_neg_one_mul_radicalElement`, `levi_neg_one_commute`,
  `determinantWeight_levi` (from `det_rankInclusion`), and
  `determinantWeight_radicalElement` (from `unipotent_det`).
- The section `Transfer` works over any topological field `K` with an additive Haar
  measure on `K^(m+1)`. It defines `transferIntegral` and `transferForm` and proves
  the translation and change-of-variables laws above. Only the sections `Support`
  and `Fourier` and the final theorem are specific to p-adic fields.
- Lattice boxes, character sums and the duality lemmas come from the helper module
  `Langlands.Representation.Derivative.MirabolicLatticeBox`.
