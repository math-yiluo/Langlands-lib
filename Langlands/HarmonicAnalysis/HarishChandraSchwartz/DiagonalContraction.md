# Contraction of block unipotent matrices by diagonal conjugation

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiagonalContraction`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.GroupScheme.Dynamic.GeneralLinear` (for `diagonalUnits` and
`blockUnipotentSubgroup`), `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Height` (for
`entryNorm`) and `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ContractionScaling`.

## Purpose and provenance

Provenance: internal. These are elementary matrix lemmas for a contraction-scaling proof of
the height comparison II.2 (6) in J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra* (2003), printed p. 254 (PDF p. 20). They are not
transcribed from Waldspurger, who derives II.2 (6) from polynomial estimates and the
closedness of unipotent orbits.

The intended use is the following. After a change of basis, a cocharacter acts diagonally
through `diag(t ^ e i)`, and the opposite unipotent radical lands in the matrices that are
block unipotent for the weights `-e`. Conjugation by a contracting torus element then
shrinks both the size of `ū` and the displacement `‖τ(ū) w − w‖` of a weight vector `w`.
This module proves the two one-step estimates and feeds them into
`exists_le_mul_pow_of_contractionScaling`. The application to actual algebraic groups is not
part of this module.

## Setting

`F` is a normed field, `n` a finite type with decidable equality, and `e : n → ℤ`.
`diagonalUnits F e t` is the invertible diagonal matrix `diag(t ^ e i)` for `t : Fˣ`.
`blockUnipotentSubgroup F (-e)` consists of the `g : GL n F` with `g i j = δ i j` whenever
`e j ≤ e i`. So the only off-diagonal entries that can be nonzero are those with
`e i < e j`. Vectors `n → F` carry the sup norm.

## Declarations

- `offIdentityNorm g` (for `Nonempty n`, `g : GL n F`) is `entryNorm (g - 1)`, the largest
  absolute value of an entry of `g - 1`. It is nonnegative (`offIdentityNorm_nonneg`) and
  vanishes at `1` (`offIdentityNorm_one`).
- `diagonalUnits_conj_apply`: the `(i, j)` entry of `D⁻¹ g D` for `D = diagonalUnits F e t`
  is `t ^ (e j - e i) * g i j`.
- `diagonalUnits_conj_mem`: `D⁻¹ g D` is block unipotent for `-e` when `g` is.
- `exists_weight_gap_le`: some `d : ℕ` satisfies `e j - e i ≤ d` whenever `e i < e j`.
- `offIdentityNorm_conj_le` (one-step contraction): if `‖t‖ ≤ 1` and `g` is block unipotent
  for `-e`, then `offIdentityNorm (D⁻¹ g D) ≤ ‖t‖ * offIdentityNorm g`.
- `offIdentityNorm_le_conj` (bounded expansion): under the same hypotheses, if `d` bounds the
  weight gaps as above, then `offIdentityNorm g ≤ ‖t‖⁻¹ ^ d * offIdentityNorm (D⁻¹ g D)`.
- `mulVec_sub_apply_eq_zero`: if `g` is block unipotent for `-e` and `w` vanishes outside
  `{k | e k = m}`, then `(g w - w) i = 0` whenever `m ≤ e i`.
- `conj_mulVec_sub_apply`: for any `g` and `w` vanishing outside `{e = m}`,
  `(D⁻¹ g D w - w) i = t ^ (m - e i) * (g w - w) i`.
- `norm_conj_mulVec_sub_le` (one-step contraction of the displacement): if `‖t‖ ≤ 1`, `g` is
  block unipotent for `-e` and `w` vanishes outside `{e = m}`, then
  `‖D⁻¹ g D w - w‖ ≤ ‖t‖ * ‖g w - w‖`.
- `exists_offIdentityNorm_le_mul_pow` (main result). Let `X` be a topological space,
  `c : X → X`, `r₀ : X → GL n F` and `r : X → GL n' F` (with `n` nonempty), `e₀ : n → ℤ`,
  `e : n' → ℤ` and `t : Fˣ` with `‖t‖ < 1`. Write `β x = offIdentityNorm (r₀ x)` and
  `q = ‖t‖⁻¹`. The hypotheses are:
  - every `r₀ x` is block unipotent for `-e₀` and every `r x` for `-e`;
  - `r₀ (c x) = D₀⁻¹ r₀ x D₀` and `r (c x) = D⁻¹ r x D`, where `D₀ = diagonalUnits F e₀ t`
    and `D = diagonalUnits F e t`;
  - `w : n' → F` vanishes outside `{e = m}`;
  - `r x w = w` implies `r₀ x = 1`;
  - `d` bounds the gaps of `e₀`;
  - the annulus `contractionScalingAnnulus β q d = {x | 1 ≤ q ^ d β x ∧ β x ≤ 1}` is compact;
  - `x ↦ ‖r x w - w‖` is continuous on this annulus.

  The conclusion is that some `C > 0` gives `β x ≤ C ‖r x w - w‖ ^ d` for every `x` with
  `1 ≤ β x`.

## Proofs as implemented

The entry formula multiplies out `diag(t ^ (-e i)) g diag(t ^ e j)` using
`Matrix.mul_diagonal`, `Matrix.diagonal_mul` and `zpow_sub₀`. Membership after conjugation
follows since the entries with `e j ≤ e i` are `δ i j`, and `t ^ 0 = 1` on the diagonal.
For `exists_weight_gap_le`, take `d` the supremum of `(e j - e i).toNat` over all pairs.

For the one-step contraction, the entries of `D⁻¹ g D - 1` with `e j ≤ e i` vanish. For
`e i < e j` the entry is `t ^ (e j - e i) g i j`, and `‖t‖ ^ (e j - e i) ≤ ‖t‖` since the
exponent is at least `1` and `‖t‖ ≤ 1` (`zpow_le_zpow_right_of_le_one₀`). Bounded expansion
uses the same entries: for `e i < e j`, `‖g i j‖ = ‖t‖⁻¹ ^ (e j - e i) ‖(D⁻¹ g D) i j‖`, and
`‖t‖⁻¹ ^ (e j - e i) ≤ ‖t‖⁻¹ ^ d` because `‖t‖⁻¹ ≥ 1`.

For the displacement, `g i k w k = δ i k w k` for all `k` when `m ≤ e i`, because `w k = 0`
unless `e k = m ≤ e i`, and then `g i k = δ i k`. The conjugation formula follows from the
entry formula, since `t ^ (e k - e i) w k = t ^ (m - e i) w k` for every `k`, and
`w i = t ^ (m - e i) w i`. For the norm bound, components with `m ≤ e i` vanish. The other
components are multiplied by `t ^ (m - e i)` with exponent at least `1`.

The main result applies `exists_le_mul_pow_of_contractionScaling` with `q = ‖t‖⁻¹` and
`D = d`:
- `β x ≤ q ^ d β (c x)` is bounded expansion;
- `q ‖r (c x) w - w‖ ≤ ‖r x w - w‖` is the displacement contraction multiplied by `‖t‖⁻¹`;
- eventual entry into `{β ≤ 1}` is `exists_iterate_le_one_of_le_mul` with `θ = ‖t‖`, using
  one-step contraction of `β`;
- positivity on the annulus: if `‖r x w - w‖ = 0`, then `r x w = w`, so `r₀ x = 1` and
  `β x = 0`, contradicting `1 ≤ q ^ d β x`.

## Scope

Nothing about algebraic groups, rational points or stabilizers is proved here. In an
application, block unipotence, conjugation equivariance, the fixed-point implication `hfix`,
compactness of the annulus and continuity must be supplied. The norms are the sup norms in
the weight bases, with no change of basis. The exponent of the inverse power bound is the
largest weight gap `d` of `e₀`.
