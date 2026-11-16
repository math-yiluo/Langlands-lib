# Signs and exponents at the positions of a list of real blocks

Module: `Langlands.Representation.Archimedean.RealBlockPositionData`, namespace
`Langlands.Archimedean.RealBlockPosition`.

## Purpose and provenance

A list `ds` of real blocks (module `StandardModule`) defines position characters
`realPositionCharacter ds i : ℝˣ → ℂ` at the positions `i = 0, 1, …`, and the real standard
module `realStandardModule N ds` is the subspace of the principal series of these characters cut
out by Fourier conditions at the induction blocks. To build intertwining maps between two
standard modules by Frobenius reciprocity (module `RealJacquetFrobeniusProof`), one needs the
position characters in the form `x ↦ sgn(x)^e |x|^t` used there, and a criterion for a
function of the principal series to lie in the standard module that only involves `O(N)`.

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealCharacterPairFiltrationStatement` (Task 7067). It contains
bookkeeping and the derived membership criterion below. It makes no literature assertion,
so it has no literature sources. The definitions `realPositionSign`,
`shiftedExponent` and `positionSign` are internal notation. The exponent function is reused
from `PrincipalSeriesGramFormula` as `GramFormula.realPositionExponent`.

## Declarations

### Signs and exponents

- `realPositionSign : List RealBlock → ℕ → Fin 2` is defined by recursion on the list. It is
  the parity of a character block. At the two positions of the real induction of a
  character of weight `m` it is `(|m| + 1) mod 2` and `0`. Past the end of the list it is `0`.
- `GramFormula.realPositionExponent : List RealBlock → ℕ → ℂ`, imported from
  `PrincipalSeriesGramFormula`, uses the same recursion. It is the
  exponent of a character block. At the two positions of an induction block of weight `m`
  and exponent `t` it is `t + |m|/2` and `t - |m|/2`. Past the end it is `0`.
- `sign_pow_eq_pow_mod_two`: `(x/|x|)^k = (x/|x|)^(k mod 2)` for real `x ≠ 0`.
- `realPositionCharacter_eq_charFun`: `realPositionCharacter ds i x =
  charFun (realPositionSign ds i) (GramFormula.realPositionExponent ds i) x` for all `ds`, `i`, `x`.
  `charFun e t` is `x ↦ sgn(x)^e |x|^t` (module `RealJacquetFrobeniusProof`). The proof is by
  recursion on the list. For an induction block it unfolds the definitions of the two
  induced characters and reduces the power of `x/|x|` modulo `2`.
- `realPositionCharacter_neg_one`: the value at `-1` is `(-1)^(realPositionSign ds i)`.
- `realPositionCharacter_exp`: the value at `exp x` is `exp(GramFormula.realPositionExponent ds i * x)`.

### Concatenation

- `realPositionSign_append`, `realPositionExponent_append`, `realInducedBlockAt_append`: at
  position `i` of `ds ++ es` these take the value of `ds` at `i` if `i < realRank ds`, and
  the value of `es` at `i - realRank ds` otherwise. Proved by recursion on `ds`.

### Induction blocks

- `realPosition_of_realInducedBlockAt`: if `realInducedBlockAt ds p = some d`, then the signs
  at `p, p + 1` are `(|m| + 1) mod 2` and `0`, and the exponents are `t + |m|/2` and
  `t - |m|/2`. Here `m = d.weight` and `t = d.exponent`.

### The `ρ`-shifted exponents

- `shiftedExponent N ds i = GramFormula.realPositionExponent ds i + (N - 1)/2 - i` for `i : Fin N`.
  `positionSign N ds i = realPositionSign ds i`.
- `expo_shiftedExponent`: removing the `ρ`-shift (`expo`, module `RealJacquetFrobeniusProof`)
  gives back `GramFormula.realPositionExponent ds i`.
- `posChar_shiftedExponent`: the characters `posChar (shiftedExponent N ds) (positionSign N ds)`
  of the Frobenius construction are the position characters of `ds` at `0, …, N - 1`.
- `principalSeries_congr`: `principalSeries ℝ N χ` only depends on `χ 0, …, χ (N - 1)`.
- `principalSeries_posChar_shiftedExponent`: hence the principal series of the
  Frobenius characters equals `principalSeries ℝ N (realPositionCharacter ds)`.
- `isExpEquivariant_shiftedExponent`: functions in that principal series satisfy
  `IsExpEquivariant (shiftedExponent N ds)` (module `RealBlockLeftDerivative`).
- `shiftedExponent_sub_of_realInducedBlockAt`: at an induction block of weight `m` at `p`,
  the shifted exponents at `p` and `p + 1` differ by `|m| + 1`.

### Membership in the standard module

- `even_of_neg_one_zpow_eq`: if `(-1)^k = (-1)^((m + 1) mod 2)` in `ℂ`, then `k + m + 1` is
  even.
- `mem_realStandardModule_of_unitaryCompact hN hf hK`: let `realRank ds = N` and let `f` be
  in the principal series of the position characters of `ds`. Suppose that at every
  induction block `d` at `p`, `Φ_k(f)(g) = blockFourierCoefficient N p k f g` vanishes for
  `|k| < |d.weight|` and all `g ∈ O(N)`. Then `f ∈ realStandardModule N ds`.
  Proof. Take `k` with `|k| < |m|`. If `(-1)^k` is the product of the two position signs at
  `-1`, then `k` lies in `window |m|` (module `RealBlockFourierPropagation`). The shifted
  exponents differ by `|m| + 1`, so `blockFourierCoefficient_window_eq_zero` extends the
  vanishing on `O(N)` of the whole window to all of `GL_N(ℝ)`. Otherwise `Φ_k(f)` vanishes
  by parity (`blockFourierCoefficient_eq_zero_of_parity`, module `RealBlockFourierFinite`).

### Lists `pre ++ ws ++ post`

- `realPositionSign_mid`, `realPositionExponent_mid`, `realInducedBlockAt_mid`,
  `realPositionCharacter_mid`: at position `realRank pre + j` with `j < realRank ws`, the
  list `pre ++ ws ++ post` has the value of `ws` at `j`.
- `realPositionSign_of_not_mid`, `realPositionExponent_of_not_mid`,
  `realInducedBlockAt_of_not_mid`, `realPositionCharacter_of_not_mid`: if
  `realRank ws = realRank ws'`, then `pre ++ ws ++ post` and `pre ++ ws' ++ post` have the
  same values at every position `i` with `i < realRank pre` or
  `realRank pre + realRank ws ≤ i`.
- `lt_of_realInducedBlockAt_of_lt`: an induction block of `pre ++ ws ++ post` that starts at
  a position `i < realRank pre` satisfies `i + 1 < realRank pre`.
- `realInducedBlockAt_one_of_realRank_eq_two`: a list of rank two has no induction block
  starting at position `1`.

All proofs are by unfolding, recursion on lists, `split_ifs` and `omega`.
