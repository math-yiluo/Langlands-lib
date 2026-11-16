# The character–induced filtration on `GL₃(ℝ)` for an induction block of weight `0`

Lean module: `Langlands.Representation.Archimedean.RealCharacterInducedWeightZero`
(namespace `Langlands.Archimedean.RealStandardFiltration`).

The Library statement `RealCharacterInducedFiltrationStatement` (module
`RealInducedPairFiltrationReduction`) asks for `RealAdjacentFiltration 3 [] [] χ D`. Here
`χ = RealBlock.character c` is a character block, `D = RealBlock.induced d` is an induction
block, and `Re t(χ) < Re t(D)`. This module proves the case `d.weight = 0`, assuming the
Library statement `RealCharacterPairFiltrationStatement` (the filtration for two adjacent
character blocks, module `RealRankOneStepFiltration`). The other cases are not treated here.
The argument is internal to the Library and cites no literature: an induction block of
weight `0` is a pair of character blocks, so two character steps do the job.

## Statements

* `kf_append_expand n pre post x`: `KF n (pre ++ x :: post) = KF n (pre ++ realBlockExpand x ++ post)`.
  This is the Library equality `realStandardModule_append_expand` (module
  `RealUnlinkedSwapReduction`) passed to the `O(n)`-finite functions. Recall that
  `realBlockExpand (RealBlock.induced d)` is
  `[RealBlock.character (charData 1 t), RealBlock.character (charData 0 t)]` when
  `d.weight = 0`, with `t = d.exponent`. Here `RealJacquetFrobenius.charData e t` is the
  character `x ↦ (x/|x|)^e |x|^t`.
* The imported `Langlands.Archimedean.realExponentSupport_append` and
  `Langlands.Archimedean.realWeightSquareSum_append` from
  `RealLanglandsRankOneReduction` give the append formulas: the exponent support and the
  sum of squared weights of `ws ++ vs` are the concatenation and the sum of those of `ws` and
  `vs`.
* `realAdjacentFiltration_character_induced_of_weight_eq_zero`: let
  `hC : RealCharacterPairFiltrationStatement`, `c : RealCharacterData` and
  `d : ComplexCharacterData`, with `d.weight = 0` and
  `realBlockExponent (RealBlock.character c) < realBlockExponent (RealBlock.induced d)`. Then
  `RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d)`.

## Proof of the weight-zero theorem

Write `χ = RealBlock.character c`, `D = RealBlock.induced d`, `t = d.exponent`,
`c₁ = RealBlock.character (charData 1 t)` and `c₂ = RealBlock.character (charData 0 t)`. Both
`c₁` and `c₂` have exponent `t`, so `Re t(χ) < Re t(cᵢ)`. Since `d.weight = 0`,
`realBlockExpand D = [c₁, c₂]`, and `kf_append_expand` gives

* `K([χ, c₁, c₂]) = K([χ, D])` (with `pre = [χ]`, `post = []`);
* `K([D, χ]) = K([c₁, c₂, χ])` (with `pre = []`, `post = [χ]`).

The exponent supports are `[s, t, t]` for `[χ, D]` (the induced block contributes
`t ± 0/2`) and `[s, t]` for `[χ, cᵢ]`, where `s = c.exponent`. The sums of squared weights of
`[χ, D]`, `[c₁]` and `[c₂]` are `0`.

By `realAdjacentFiltration_iff`, the goal is
`HasFiltration 3 [χ, D] (IsAdjacentPiece [] [] χ D)`.

1. `hC` for `pre = []`, `post = [c₂]` and the characters `c`, `charData 1 t` gives
   `RealAdjacentFiltration 3 [] [c₂] χ c₁`, a filtration of `K([χ, c₁, c₂])`. By
   `realAdjacentFiltration_iff` it is a `HasFiltration` with pieces
   `IsAdjacentPiece [] [c₂] χ c₁`. It is refined by `HasFiltration.bind`, and the result is
   transported to `K([χ, D])` by `HasFiltration.congr`. So it suffices to filter every piece
   `ws ++ [c₂]` by pieces satisfying `IsAdjacentPiece [] [] χ D`.
2. Piece `ws = [c₁, χ]`, that is, the list `[c₁, χ, c₂]`. Apply `hC` for `pre = [c₁]`,
   `post = []` and the characters `c`, `charData 0 t`. This filters `K([c₁, χ, c₂])` with
   pieces `IsAdjacentPiece [c₁] [] χ c₂`. Then `HasFiltration.of_eq_pieces` replaces these
   pieces as follows.
   * The piece `[c₁, c₂, χ]` is replaced by `[D, χ]`, which has the same `O(n)`-finite
     functions. The list `[D, χ]` is an `IsAdjacentPiece [] [] χ D` with `ws = [D, χ] = [y, x]`.
   * A piece `[c₁] ++ ws'` with `realExponentSupport ws'` a permutation of `[s, t]` and
     `0 < realWeightSquareSum ws'` stays. Its exponent support `t :: support(ws')` is a
     permutation of `[t, s, t]`, hence of `[s, t, t]` (swap the first two entries). Its sum
     of squared weights is `0 + realWeightSquareSum ws' > 0`. So it is an
     `IsAdjacentPiece [] [] χ D` with `ws = c₁ :: ws'`.
3. A piece `ws ++ [c₂]` with `realExponentSupport ws` a permutation of `[s, t]` and
   `0 < realWeightSquareSum ws` is already an `IsAdjacentPiece [] [] χ D`, with
   `ws ++ [c₂]` in the role of `ws`. Its exponent support `support(ws) ++ [t]` is a
   permutation of `[s, t] ++ [t] = [s, t, t]`. Its sum of squared weights is
   `realWeightSquareSum ws + 0 > 0`. It gets the one-piece filtration
   (`HasFiltration.self`).
