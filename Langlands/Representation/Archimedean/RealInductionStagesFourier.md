# Fourier conditions on `O(N)` suffice for real standard modules

Module: `Langlands.Representation.Archimedean.RealInductionStagesFourier`.

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealAdjacentFiltrationInStagesStatement` (induction in stages of adjacent
filtrations, Task 7068). The Library's `realStandardModule N ds` asks a principal-series
function `f` to have vanishing block Fourier coefficients at every `g ∈ GL_N(ℝ)`. Functions
built by induction in stages are only controlled on `O(N)`. The main theorem shows that
vanishing on `O(N)` suffices.

The module makes no literature assertion. It combines two Library results:

- `RealBlockPropagation.blockFourierCoefficient_window_eq_zero` (module
  `RealBlockFourierPropagation`) propagates the vanishing from `O(N)` to `GL_N(ℝ)` for the
  modes in the window `|j| < m`, `j + m + 1` even.
- `RealBlockFourierFinite.blockFourierCoefficient_eq_zero_of_parity` makes the modes of the
  other parity vanish everywhere.

All declarations are in the namespace `Langlands.Archimedean.InductionStages`.

## Declarations

- `realPositionCharacter_exp ds l x`: `χ_l(e^x) = e^(τ_l x)` for the position character
  `χ_l = realPositionCharacter ds l` and exponent `τ_l = realPositionExponent ds l`. Proof: by
  `realPositionCharacter_eq_signUnit_mul`, `χ_l(y) = χ_l(sgn y) |y|^(τ_l)`. Here `sgn(e^x) = 1`,
  `χ_l(1) = 1` (`RealStrictCharacterLanglandsQuotient.realPositionCharacter_one`), and
  `(e^x)^τ = e^(xτ)` (`RealPrincipalSeriesDuality.ofReal_exp_cpow`).
- `realPosition_of_realInducedBlockAt`: if `ds` has an induction block `d` at position `p`,
  then the characters at positions `p` and `p + 1` are `realInducedFirstCharacter d` and
  `realInducedSecondCharacter d`. The exponents there are `t + |m|/2` and `t - |m|/2`, where
  `t = d.exponent` and `m = d.weight`. Proof by induction on the list.
- `realInducedFirstCharacter_neg_one`: the first character takes the value `(-1)^(|m|+1)` at
  `-1`. `realInducedSecondCharacter_neg_one`: the second takes the value `1` there.
- `mem_realStandardModule_of_unitaryCompact hN hf hK`: let `realRank ds = N`, and let
  `f ∈ principalSeries ℝ N (realPositionCharacter ds)`. Suppose that for every induction block
  `d` of `ds` at a position `p`, every `k : ℤ` with `|k| < |d.weight|` and every `κ ∈ O(N)`,
  the coefficient `blockFourierCoefficient N p k f κ` vanishes. Then
  `f ∈ realStandardModule N ds`.

  Proof. Fix a block `d` at `p`, with `M = |d.weight|`, and `|k| < M`. By `realInducedBlockAt_lt`
  and `hN`, `p + 1 < N`.
  - If `k + M + 1` is even, `k` lies in the window of `M`. `f` is exp-equivariant
    (`RealBlockDerivative.isExpEquivariant_of_mem_principalSeries`, with `τ` the position
    exponents and `realPositionCharacter_exp`), with shifted exponents
    `α_i = τ_i + (N - 1)/2 - i`. Then `α_p - α_(p+1) = (t + M/2) - (t - M/2) + 1 = M + 1`. The
    window hypotheses on `O(N)` follow from `hK`. So
    `blockFourierCoefficient_window_eq_zero` gives the vanishing at every `g`.
  - Otherwise `k + M + 1` is odd. By the parity lemma, the coefficient vanishes unless
    `(-1)^k = χ_p(-1) χ_(p+1)(-1) = (-1)^(M+1)`. If these were equal, then
    `-1 = (-1)^(k+M+1) = (-1)^k (-1)^(M+1) = ((-1)^(M+1))^2 = 1`, a contradiction.
