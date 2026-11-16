# The filtration for two real characters in the reducible case

Module: `Langlands.Representation.Archimedean.RealCharacterPairReducible`, namespace
`Langlands.Archimedean.RealCharacterPairReducible`.

## Purpose and provenance

Let `c = sgn^{e_c} |·|^{t_c}` and `d = sgn^{e_d} |·|^{t_d}` be characters of `ℝ^×`
(`RealCharacterData`), let `ε = pairParity c d ∈ {0, 1}` (module `RealCharacterPairData`), and
let `pre`, `post` be lists of real blocks with
`realRank (pre ++ character c :: character d :: post) = n`. This module proves
`RealAdjacentFiltration n pre post (character c) (character d)` (module
`RealRankOneStepFiltration`) in the **reducible case**: `t_d - t_c = ℓ` for a natural number
`ℓ > 0` with `ℓ - 1 ≡ ε (mod 2)`. In this case the principal series of `GL_2(ℝ)` with exponents
`(t_c, t_d)` is reducible. The filtration has two pieces: the swapped pair `[d, c]` and the real
induction of the complex character `pairInduced c d ℓ`, which has weight `ℓ`.

The statement `RealCharacterPairFiltrationStatement` covers the reducible case and the generic
case. This module proves the reducible case and reduces the statement to the generic case
(`realCharacterPairFiltration_of_generic`). The generic case is proved in module
`RealCharacterPairFiltration` with `data_swap` and `data_unswap` from this module. All maps
are built by Frobenius reciprocity
with block multipliers (module `RealBlockFrobeniusMap`). The multipliers are the binomial and
tail multipliers of module `RealBlockMultiplier`. The module is internal infrastructure for the
proof of `Langlands.Archimedean.RealCharacterPairFiltrationStatement` (Task 7067), so it has no
literature sources. It contains no definitions of mathematical objects: `cd`, `dc`, `indBlock`
and `sigma0` below are notation.

## Notation

- `src = pre ++ character c :: character d :: post`, the list whose standard module is
  filtered.
- `swp = pre ++ dc c d ++ post` with `dc c d = [character d, character c]`, and
  `cd c d = [character c, character d]`.
- `ind = pre ++ indBlock c d ℓ ++ post` with
  `indBlock c d ℓ = [induced (pairInduced c d ℓ)]`.
- `K(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`.
- `p = realRank pre`, the position of the pair. All Frobenius maps are along the block
  `(p, p + 1)`.
- `sigma0 c d = (-1)^{ε.natAbs}`, the symmetry sign of the binomial multiplier (and of the
  generic multiplier used in module `RealCharacterPairFiltration`). `sigma0_eq` shows
  that it equals `(-1)^{e_c} (-1)^{e_d}`, and `sigma0_inv` shows that it is its own inverse.

## Declarations

### General facts about Frobenius maps

- `IsRealIntertwinerModulo.mono`: an intertwiner modulo `M` is an intertwiner modulo every
  `N ≥ M`.
- `isRealIntertwinerModulo_of_leftInverse h h' hrec' hinv M hM`: let
  `q = blockFrobMap h : K(ds) → K(es)` (multiplier `μ`, no recurrence assumed) and
  `D = blockFrobMap h' : K(es) → K(ds)` (multiplier `μ'`, recurrent for the exponents of
  `es`, hence an intertwiner). If `D (q f) = f` for every `f` and `ker D ≤ M`, then `q` is an
  intertwiner modulo `M`. Proof: `q` commutes with right translations by `O(n)`
  (`blockFrobMap_mk_rightTranslation`), so the translation defect is `0`. For the derivative
  defect `h_X = q (R_X f) - R_X (q f)`, `D` commutes with `R_X` and `D ∘ q = id`, so
  `D h_X = R_X f - R_X f = 0` and `h_X ∈ ker D ≤ M`.
- `blockFourierCoefficient_zero`: the block Fourier coefficients of `0` vanish.
- `ker_le_range h₀ hB hD hsupp`: let `q = blockFrobMap h₀ : K(ds) → K(es)` (multiplier
  `μ`), `B = blockFrobMap hB : K(es) → K(ds)` (multiplier `μ'`) and
  `D = blockFrobMap hD : K(es) → K(fs)` (multiplier `P`), all along `p` with parity `ε`.
  Assume `P_j ≠ 0` for every `j` of the parity class with `μ_j μ'_j ≠ 1`. Then
  `ker D ≤ range q`. Proof: for `D g = 0`, `P_j Φ_j(g) = Φ_j(D g) = 0` on `O(n)`, so
  `Φ_j(g) = 0` on `O(n)` whenever `μ_j μ'_j ≠ 1`. By `blockFrobMap_blockFrobMap_eq`,
  `q (B g) = g`.

### Signs and positions

- `inv_eq_self_of_sq_eq_one`, `neg_one_pow_sq_fin`, `neg_one_pow_natAbs`,
  `neg_one_pow_succ_mod_two` (`(-1)^{(ℓ + 1) % 2} = (-1)^ε` when `ℓ - 1 ≡ ε`), and
  `neg_one_pow_pairParity'` (`(-1)^ε = (-1)^{e_c} (-1)^{e_d}`): sign identities.
- `exponent_mid_zero`, `exponent_mid_one`, `realRank_mid_eq`, `mid_pair`
  (`pre ++ [x, y] ++ post = pre ++ x :: y :: post`): positions of `pre ++ ws ++ post` at `p`
  and `p + 1`.
- `realRank_cd`, `realRank_dc`, `realRank_indBlock` (all `2`) and `realRank_dc_mid`,
  `realRank_cd_mid`, `realRank_ind_mid` (the three lists `swp`, `src` written as
  `pre ++ cd c d ++ post`, and `ind` have rank `n`).
- `exponent_indBlock_zero`, `exponent_indBlock_one`: for `t_d - t_c = ℓ`, the exponents of
  `indBlock c d ℓ` at positions `0, 1` are `(t_c + t_d)/2 ± ℓ/2`, that is `t_d` and `t_c`.
- `sign_indBlock_zero`, `sign_indBlock_one`: the signs of `indBlock c d ℓ` at positions
  `0, 1` are `(ℓ + 1) mod 2` and `0`.

### The Frobenius data

All are proved with `IsBlockFrobData.of_mid`. Its sign conditions reduce to the identities
above.

- `data_swap hn hsym`: for every multiplier `μ` with `hsym : IsSymmetric ε (sigma0 c d) μ`,
  `IsBlockFrobData n swp src p ε (sigma0 c d) μ`. The field `induced_p` is vacuous because
  `src` has a character block at `p`.
- `data_unswap hn hsym`: for the same `μ`,
  `IsBlockFrobData n src swp p ε (sigma0 c d)⁻¹ μ⁻¹`, with the pointwise inverse multiplier
  (symmetric for `(sigma0 c d)⁻¹` by `IsSymmetric.inv`).
- `data_q0`: `data_swap` for `binomialMultiplier ℓ ε`. This gives `q₀ : K(swp) → K(src)`.
- `data_B`: `data_unswap` for `binomialMultiplier ℓ ε`. This gives `B : K(src) → K(swp)`.
- `exponent_swp_zero`, `exponent_swp_one`: the exponents of `swp` at `p` and `p + 1` are
  `t_d` and `t_c`.
- `data_D hn hℓ hpar hν`: `IsBlockFrobData n src ind p ε ((-1)^{e_d})
  (tailMultiplier ℓ ε ((-1)^{e_d}))`. This gives `D : K(src) → K(ind)`. The field
  `induced_p`, which says that the multiplier vanishes on the window `|j| < ℓ` of the induced
  block, holds because the tail multiplier is nonzero only for `ℓ < |j|`.
- `data_q1 hn hℓ hpar hν`: `IsBlockFrobData n ind src p ε ((-1)^{e_d})⁻¹
  (tailMultiplier ℓ ε ((-1)^{e_d}))⁻¹`. This gives `q₁ : K(ind) → K(src)`.

### The filtration

- `abs_lt_of_parity`: if `ℓ - 1 ≡ ε` and `j ≡ ε (mod 2)`, then `|j| ≤ ℓ` implies `|j| < ℓ`.
  The parities of `j` and `ℓ` differ, so `|j| = ℓ` is impossible.
- **`realAdjacentFiltration_of_reducible hn hℓ hpar hν`**: for
  `hn : realRank src = n`, `hℓ : 0 < ℓ`, `hpar : Even (ℓ - 1 - ε)` and
  `hν : t_d - t_c = ℓ`, `RealAdjacentFiltration n pre post (character c) (character d)` holds,
  with `k = 2`, `ws 0 = [character d, character c]`,
  `ws 1 = [induced (pairInduced c d ℓ)]`, `q 0 = q₀` and `q 1 = q₁`.
- **`realCharacterPairFiltration_of_generic hgen`**: `RealCharacterPairFiltrationStatement`
  holds if `hgen` gives `RealAdjacentFiltration n pre post (character c) (character d)` for all
  `n`, `pre`, `post`, `c`, `d` with `realRank src = n`, `Re t_c < Re t_d` and
  `t_d - t_c ≠ ε + 2m + 1` for every `m : ℕ`. Proof: by `generic_or_reducible`, either this
  generic condition holds, and `hgen` applies, or `t_d - t_c = ℓ` with `ℓ > 0` and
  `ℓ - 1 ≡ ε`, and `realAdjacentFiltration_of_reducible` applies.

## Proof of `realAdjacentFiltration_of_reducible`

The ρ-shifted exponent differences are `δ = t_d - t_c + 1 = ℓ + 1` for `swp` and
`δ = t_c - t_d + 1 = 1 - ℓ` for `src`.

1. **Recurrences.** The binomial multiplier is recurrent for `ℓ + 1`
   (`isRecurrent_binomialMultiplier`), so `q₀` is an intertwiner
   (`isRealIntertwinerModulo_blockFrobMap`). The tail multiplier is recurrent for `1 - ℓ`
   (`isRecurrent_tailMultiplier`), so `D` is an intertwiner.
2. **`D ∘ q₁ = id`.** The product of the tail multiplier and its inverse is `1` wherever the
   tail multiplier is nonzero. On the parity class it vanishes exactly for `|j| ≤ ℓ`, hence for
   `|j| < ℓ` by `abs_lt_of_parity`. For `f ∈ K(ind)`, `Φ_j(f) = 0` for these `j`: the
   standard module of `ind` satisfies the Fourier condition of the induced block
   `pairInduced c d ℓ` at position `p` (`realInducedBlockAt_mid`), and its weight is `ℓ`.
   So `blockFrobMap_blockFrobMap_eq` gives `D (q₁ f) = f`.
3. **`ker D ≤ range q₀`.** Use `ker_le_range` with `B`. Where `μ_j μ_j⁻¹ ≠ 1`, the
   binomial multiplier vanishes, so `|j| ≥ ℓ` (`binomialMultiplier_ne_zero_iff`). Then
   `|j| > ℓ` by `abs_lt_of_parity`, and the tail multiplier is nonzero there
   (`tailMultiplier_ne_zero_iff`).
4. **The pieces.** `ws 0 = [d, c]` is the first alternative of `RealAdjacentFiltration`.
   `ws 1` has exponent support `[t_d, t_c]`, a permutation of `[t_c, t_d]`
   (`realExponentSupport_pairInduced`), and squared-weight sum `ℓ² > 0`
   (`realWeightSquareSum_lt_pairInduced`).
5. **Intertwiners modulo the earlier ranges.** `q₀` is an intertwiner (step 1). `q₁` is an
   intertwiner modulo `ker D` by `isRealIntertwinerModulo_of_leftInverse` (steps 1 and 2). By
   step 3, `ker D ≤ range q₀ = ⨆_{i < 1} range (q i)`.
6. **Spanning.** For `g ∈ K(src)`, `g - q₁ (D g) ∈ ker D` by step 2, so it equals `q₀ a` for
   some `a` by step 3. Hence `g = q₀ a + q₁ (D g)` lies in `range q₀ ⊔ range q₁`.

Axioms of `realAdjacentFiltration_of_reducible` and `realCharacterPairFiltration_of_generic`: `propext`, `Classical.choice`, `Quot.sound`.
