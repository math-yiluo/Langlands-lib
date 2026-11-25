# Splitting the induction blocks of a real standard module

Module `Langlands.Representation.Archimedean.RealSplitFrobenius`, namespace
`Langlands.Archimedean.RealSplitFrobenius`.

## Purpose and provenance

For a list `ds` of real blocks (module `StandardModule`), `split ds` replaces every induction
block `.induced e` (weight `m = e.weight`, exponent `t = e.exponent`, `ℓ = |m|`) by the two
character blocks

- `lowChar e = |·|^(t - ℓ/2)` (sign `0`), then
- `highChar e = sgn^(ℓ+1) |·|^(t + ℓ/2)`,

in this order. Character blocks are kept. The main result `exists_splitMap` gives a
surjective intertwiner `D : K(split ds) → K(ds)` with a right inverse `Q` that commutes with
`O(n)`, and describes the kernel of `D` through block Fourier modes.

Notation: `K(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, the
`O(n)`-finite functions of the real standard module; `Φ^p_j = blockFourierCoefficient n p j`
is the `j`-th Fourier coefficient along the rotation block at positions `p, p + 1` (Library
module `RealBlockFourierFinite`); `realInducedBlockAt ds p` is the induction block of `ds` at
position `p`, if any (module `RealBlockPositionData`).

This module is internal infrastructure for the reverse-intertwiner step of the proof of
`RealStandardIrreducibleCriterionStatement` (`RealReverseIntertwinerKernelStatement`, module
`RealStandardIrreducibleCriterionReduction`)
when `ds` has induction blocks. It has no literature source. The idea is classical: an
induction block of weight `m` is the irreducible subquotient of the principal series of its
two characters that contains the `O(2)`-types of weight `≥ ℓ`; here this is realised by the
Frobenius maps of module `RealBlockFrobeniusMap` and the tail multipliers of the Library
module `RealBlockMultiplier`, which were built for the proof of
`RealCharacterPairFiltrationStatement`. The order low/high of the two characters is the
order used by `data_D` of module `RealCharacterPairReducible` (exponent difference `ℓ`).
`split`, `IsTailFrom`, `IsSplitMap` and `Commutes` are internal notation.

## The split list

- `splitParity ℓ = (ℓ + 1) mod 2` (as an integer) and `splitSign ℓ = (-1)^((ℓ + 1) mod 2)`:
  the parity class of the block modes of the two characters, and the sign of the symmetry
  of the multipliers.
- `lowChar e`, `highChar e`, `splitBlock`, `split`: as above (`splitBlock (.character c) =
  [.character c]`, `split` maps `splitBlock` over the list and concatenates).
- `realRank_append'`, `realRank_splitBlock`, `realRank_split`: `split` keeps the rank.
- `splitParity_eq`: `splitParity ℓ ∈ {0, 1}`; `even_splitParity`:
  `ℓ - 1 - splitParity ℓ` is even; `splitSign_sq`: `splitSign ℓ ^ 2 = 1`;
  `neg_one_zpow_splitParity`: `(-1)^(splitParity ℓ) = splitSign ℓ`.

## Multipliers

`exists_unsplitMultiplier ℓ`: there is `μ : ℤ → ℂ` that is symmetric
(`IsSymmetric (splitParity ℓ) (splitSign ℓ) μ`), satisfies the recurrence
`IsRecurrent (1 - ℓ) (splitParity ℓ) μ`, and on the parity class vanishes exactly on the
window `|j| < ℓ`. For `ℓ > 0` this is the Library `tailMultiplier ℓ ε σ` with its lemmas
`isSymmetric_tailMultiplier`, `isRecurrent_tailMultiplier`, `tailMultiplier_ne_zero_iff`
(and `abs_lt_of_parity` of `RealCharacterPairReducible` for the boundary mode `|j| = ℓ`). For
`ℓ = 0` the parity class is odd and `μ = genericMultiplier 0 1` of module
`RealBlockMultiplierGeneric`, which never vanishes there (`genericMultiplier_ne_zero_of_ne`,
`isRecurrent_genericMultiplier_of_ne`).

## The Frobenius data along one induction block

For `pre ++ [.induced e] ++ post` of rank `n`, with `ℓ = |e.weight|` and `p = realRank pre`:

- `realRank_splitBlock_mid`: `pre ++ splitBlock (.induced e) ++ post` has the same rank.
- `data_unsplit hn hsym hzero`: for a symmetric `μ` vanishing on the parity class exactly on
  `|j| < ℓ`, `IsBlockFrobData n (pre ++ splitBlock (.induced e) ++ post)
  (pre ++ [.induced e] ++ post) p (splitParity ℓ) (splitSign ℓ) μ`. So the Frobenius map goes
  from the split list to the list with the induction block.
- `data_resplit hn hsym`: `IsBlockFrobData` in the other direction, with sign
  `(splitSign ℓ)⁻¹` and multiplier `j ↦ (μ j)⁻¹`.

Both are `IsBlockFrobData.of_mid` of module `RealBlockFrobeniusMap`; the exponent, sign and
parity conditions are computed from `lowChar`, `highChar` and `charData`.

## Maps that commute with the actions

- `Commutes n D` (for `D : K(xs) →ₗ[ℂ] K(ys)`): `D` commutes with the right translations by
  `O(n)` (`realStandardRep`) and with the derivatives `1 ⊗ X` for real `X`
  (`realStandardLie`).
- `commutes_id`, `Commutes.comp`.
- `commutes_blockFrobMap h hrec`: a Frobenius map whose multiplier satisfies the recurrence
  for `t_p - t_{p+1} + 1` commutes with the actions (`blockFrobMap_rightTranslation`,
  `blockFrobMap_rightDerivative`).
- `Commutes.isRealStandardIntertwiner`: such a map is an `IsRealStandardIntertwiner` into the
  standard module of `ys` (the complexified Lie action is determined by the real one).

## Fourier modes on `O(n)`

- `blockFourierCoefficient_eq_zero_of_eqOn`: if `F` vanishes on `O(N)`, so do all its block
  Fourier coefficients.
- `blockFourierCoefficient_blockFrobMap_eq_zero h hd f i h0 hk`: a Frobenius map along the
  block `p` keeps the vanishing on `O(n)` of `Φ^{p'}_i` for a disjoint block `p'`
  (`p + 1 < p'` or `p' + 1 < p`). Proof: on `O(n)` the map is the finite sum
  `(2π)⁻¹ Σ_j μ_j Φ^p_j(f)` (`frobFun_apply_of_mem`, `exists_bound_coe`), and Fourier
  coefficients along disjoint blocks commute (`blockFourierCoefficient_comm`).
- `integral_mul_eq_zero_of_modes hp ha haK hF hFK h` (Parseval orthogonality): let `a`, `F`
  be continuous `O(N)`-finite functions and suppose that for every `j` either `Φ^p_j a` or
  `Φ^p_{-j} F` vanishes on `O(N)`. Then `∫_{O(N)} a F = 0`. Proof: expand `a` and `F` in
  block Fourier coefficients (`exists_eq_sum_blockFourierCoefficient`). A term with
  `j + j' = 0` vanishes by hypothesis. For `j + j' ≠ 0`, left translation by the block
  rotation of angle `π / (j + j')` multiplies `Φ^p_j a · Φ^p_{j'} F` by `-1`
  (`blockFourierCoefficient_blockRotation_mul`), so by left invariance of Haar measure the
  integral equals its negative.

## The split map

- `IsTailFrom n r ys a`: for every induction block `d` of `ys` at a position `p ≥ r` and
  every `|j| < |d.weight|`, `Φ^p_j a` vanishes on `O(n)`.
- `IsSplitMap n pre xs ys D Q`: `Commutes n D`; `Q` commutes with `O(n)`; `D ∘ Q = id`; `Q`
  keeps the vanishing on `O(n)` of `Φ^{p'}_j` for blocks `p' + 1 < realRank pre`; and every
  continuous `O(n)`-finite `a` with `IsTailFrom n (realRank pre) ys a` satisfies
  `∫_{O(n)} a f = 0` for all `f ∈ ker D`.
- `exists_isSplitMap ds pre xs ys`: if `xs = pre ++ split ds`, `ys = pre ++ ds` and
  `realRank ys = n`, there are `D`, `Q` with `IsSplitMap n pre xs ys D Q`. Induction on `ds`
  (the equations for `xs`, `ys` avoid casts between standard modules):
  - `[]`: `D = Q = id`.
  - a character block: move it into `pre`.
  - an induction block `e` at `p = realRank pre`, `mid = pre ++ splitBlock (.induced e) ++ ds`:
    the induction hypothesis gives `D', Q'` from `xs` to `mid`. Put
    `D = blockFrobMap (data_unsplit …) ∘ D'` and `Q = Q' ∘ blockFrobMap (data_resplit …)`.
    The recurrence for `μ` at the exponents of `mid` is `IsRecurrent (1 - ℓ)`, since the
    exponent difference of `lowChar e` and `highChar e` is `-ℓ`. `D ∘ Q = id` by
    `blockFrobMap_blockFrobMap_eq`: `μ⁻¹ μ = 1` off the window `|j| < ℓ`, and the window modes
    of an element of `K(ys)` vanish (Fourier condition of the induction block). For the
    kernel: if `D f = 0`, then `g = D' f` has `Φ^p_j g = 0` on `O(n)` for `|j| ≥ ℓ`
    (`μ_j ≠ 0` there, `blockFourierCoefficient_blockFrobMap`; off the parity class by
    `blockFourierCoefficient_eq_zero_of_not_even`), hence so has `Q' g`. Write
    `f = (f - Q' g) + Q' g`. The first summand lies in `ker D'` and is handled by the
    induction hypothesis; for the second, `integral_mul_eq_zero_of_modes` at the block `p`
    applies, since `a` has no modes `|j| < ℓ` there.
- **`exists_splitMap ds hn`** (`hn : realRank ds = n`): there are linear maps
  `D : K(split ds) → K(ds)` and `Q : K(ds) → K(split ds)` such that
  1. `D` is an `IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds)
     (split ds) D`;
  2. `Q (realStandardRep n ds k h) = realStandardRep n (split ds) k (Q h)` for `k ∈ O(n)`;
  3. `D (Q h) = h` for all `h` (so `D` is onto);
  4. for every continuous `O(n)`-finite `a : GL_n(ℝ) → ℂ` such that `Φ^p_j a` vanishes on
     `O(n)` whenever `ds` has an induction block `d` at `p` and `|j| < |d.weight|`, and every
     `f` with `D f = 0`: `∫_{O(n)} a f = 0`.

  This is `exists_isSplitMap` with `pre = []`.
