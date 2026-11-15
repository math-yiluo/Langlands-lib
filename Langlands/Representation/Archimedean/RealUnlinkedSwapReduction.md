# Reducing unlinked swaps of real blocks to four kinds of pairs

Lean module: `Langlands.Representation.Archimedean.RealUnlinkedSwapReduction`.

The Library statement `Langlands.Archimedean.RealUnlinkedSwapStatement` (Swap, module
`RealStandardIrreducibleCriterionReduction`) is one of the two statements to which that module
reduces the "if" direction of Speh's criterion (Mœglin 1997, Theorem 10b, printed p. 164).
Swap says: for lists `pre`, `post` of real blocks and real blocks `x`, `y` with
`realRank (pre ++ x :: y :: post) = n`, `realBlockExponent y ≤ realBlockExponent x` and
`AreRealBlocksUnlinked x y`, there is an injective intertwiner
`I(pre ++ x :: y :: post) → I(pre ++ y :: x :: post)`
(`RealInjectiveIntertwinerExists n (pre ++ x :: y :: post) (pre ++ y :: x :: post)`).

This module states four special cases of Swap, one for each kind of the two exchanged
blocks, where an induction block always has nonzero weight, and proves that the four cases
imply Swap (`realUnlinkedSwapReduction`). The four cases are only stated here; they still
need proofs.

Notation as in `RealStandardIrreducibleCriterionReduction.md`: `I(ds)` is the
`(𝔤𝔩_n(ℝ), O(n))`-module `(realStandardRep n ds, realStandardLie n ds)` on
`kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, and
`RealInjectiveIntertwinerExists n ds es` says that there is an injective `ℂ`-linear map
`T : I(ds) → I(es)` with `IsRealStandardIntertwiner n (realStandardRep n es)
(realStandardLie n es) ds T`. A block of the Library is `RealBlock.character c` (a real
character `c : RealCharacterData`, rank `1`) or `RealBlock.induced d` (the real induction of a
complex character `d : ComplexCharacterData`, rank `2`); its real exponent is
`realBlockExponent`, the real part of its exponent.

## The four statements

All four have the same shape as Swap: the lists `pre`, `post` are arbitrary, the rank of
`pre ++ x :: y :: post` is `n`, the real exponent of the second block is at most that of the
first, the two blocks are unlinked (`AreRealBlocksUnlinked`), and the conclusion is
`RealInjectiveIntertwinerExists n (pre ++ x :: y :: post) (pre ++ y :: x :: post)`.

1. `RealCharacterSwapStatement`: `x = RealBlock.character a`, `y = RealBlock.character b` for
   real characters `a`, `b`.
2. `RealCharacterInducedSwapStatement`: `x = RealBlock.character a`, `y = RealBlock.induced e`
   with `e.weight ≠ 0`.
3. `RealInducedCharacterSwapStatement`: `x = RealBlock.induced d` with `d.weight ≠ 0`,
   `y = RealBlock.character b`.
4. `RealInducedSwapStatement`: `x = RealBlock.induced d`, `y = RealBlock.induced e` with
   `d.weight ≠ 0` and `e.weight ≠ 0`.

`RealUnlinkedSwapReductionStatement` is the implication
`RealCharacterSwapStatement → RealCharacterInducedSwapStatement →
RealInducedCharacterSwapStatement → RealInducedSwapStatement → RealUnlinkedSwapStatement`.

Source. Each of the four statements is the case of Swap for blocks of fixed kinds, so they
are true when Swap is (`RealStandardIrreducibleCriterionReduction.md` explains why Swap is
true). By `RealLargeStandardIrreducibleReduction.md`, a character block is a datum
`(1, t, sgn^ε)` of Mœglin (§10, p. 164) and an induction block of nonzero weight `m` is a
discrete series datum `(2, t, D_|m|)`. The exchanged pair `[x, y]` then lives on
`GL_{r_x + r_y}(ℝ)` with `r_x + r_y = 2, 3, 3, 4` in the four cases. These are the groups
`GL(a)`, `a = 2, 3, 4`, to which Mœglin reduces the proof of Theorem 10b ("To prove this last
theorem, using the method explained here, one reduces to GL(a) with a = 2, 3, or 4. These
cases are done in [Sp1]", p. 165). Case 1 is the `GL_2` case of her §§7–8 (Proposition 7,
p. 162; §8, p. 163). The split into the four statements is internal to this module.

## Induction blocks of weight zero

An induction block `RealBlock.induced d` with `d.weight = 0` and exponent `t = d.exponent` is
not a discrete series block. Its Mœglin data are two characters,
`[character 1 t, character 0 t]` (`realBlockMoeglinData`), and the Library describes it as the
full principal series `Ind(sgn |·|^t ⊗ |·|^t)` of `GL_2(ℝ)` (`StandardModule.md`, item 3).
This module makes this precise at the level of standard modules: replacing such a block by
the two character blocks `sgn |·|^t`, `|·|^t` does not change the standard module, as a space
of functions on `GL_n(ℝ)`.

* `realBlockExpand x`: for `x = RealBlock.induced d` with `d.weight = 0` it is the list
  `[RealBlock.character (charData 1 t), RealBlock.character (charData 0 t)]`, where
  `RealJacquetFrobenius.charData e t` is the real character `x ↦ (x/|x|)^e |x|^t` with parity
  `e` and exponent `t`; every other block `x` gives `[x]`.
* `realStandardModule_append_expand`: `realStandardModule n (pre ++ x :: post) =
  realStandardModule n (pre ++ realBlockExpand x ++ post)`.

Proof. `realStandardModule n ds` is the set of functions in the principal series with the
position characters `realPositionCharacter ds` that satisfy the Fourier conditions
`blockFourierCoefficient n p k f g = 0` for every induction block `d` at position `p`
(`realInducedBlockAt ds p = some d`) and every `|k| < |d.weight|`
(`mem_realStandardModule_iff`). For a block of weight `0` there is no such `k`, so the
condition of that block is empty. The position characters of the block are
`realInducedFirstCharacter d = (x/|x|)^(0+1) |x|^(t+0)` and
`realInducedSecondCharacter d = |x|^(t-0)`, which are the characters of `charData 1 t` and
`charData 0 t`. The lemmas:

* `realPositionCharacter_append_congr`, `realInducedBlockAt_append_congr`: equalities of
  position characters, and reflexive relations between the induction blocks at each position,
  pass from `A`, `B` to `pre ++ A`, `pre ++ B` (induction on `pre`).
* `InducedBlockRelation o o'`: every induction block of `o'` is one of `o`, and every
  induction block of nonzero weight of `o` is one of `o'`.
* `realStandardModule_eq_of_inducedBlockRelation`: two lists with the same position characters
  and related induction blocks at every position have the same standard module.

Further lemmas on the expansion: `realRank_realBlockExpand` (the expansion has the rank of the
block), `realBlockExponent_of_mem_expand` (every block of the expansion has the real exponent
of the block), `isRealBlockNondegenerate_of_mem_expand` (every block of the expansion is
nondegenerate: `IsRealBlockNondegenerate` holds for character blocks and for induction blocks
of nonzero weight), `mem_realBlockMoeglinData_of_mem_expand` (the Mœglin data of the blocks
of the expansion are Mœglin data of the block) and `areRealBlocksUnlinked_of_mem_expand`
(blocks of the expansions of two unlinked blocks are unlinked). The reused lemma `Langlands.LocalFactor.Archimedean.realRank_append`
from `ArchimedeanPairFactor`
is `realRank (xs ++ ys) = realRank xs + realRank ys`.

## Transport and moving blocks

* `exists_linearEquiv_coe_eq`: equal submodules of functions are linearly equivalent by the
  identity on functions.
* `RealInjectiveIntertwinerExists.of_eq`: if `realStandardModule n ds =
  realStandardModule n ds'` and `realStandardModule n es = realStandardModule n es'`, then
  `RealInjectiveIntertwinerExists n ds es` implies `RealInjectiveIntertwinerExists n ds' es'`.
  The actions of `O(n)` and `𝔤𝔩_n(ℝ)` on `I(ds)` are right translation and right derivative
  of the underlying functions (`realStandardRep_apply_coe`,
  `realStandardLie_one_tmul_apply_coe`), so the composite of `T` with the two identities on
  functions is again an injective intertwiner.
* `IsRealSwappable a b`: `a` and `b` are nondegenerate, `realBlockExponent b ≤
  realBlockExponent a` and `AreRealBlocksUnlinked a b`.
* `realInjectiveIntertwinerExists_swap`: the four statements give the swap of any two
  swappable blocks (case split on the kinds of `a` and `b`).
* `realInjectiveIntertwinerExists_moveToEnd'`: given swaps of swappable blocks, a block `a`
  swappable with every block of a list `l` moves past `l`:
  `RealInjectiveIntertwinerExists n (pre ++ a :: l ++ post) (pre ++ l ++ a :: post)`
  (induction on `l`, as `realInjectiveIntertwinerExists_moveToEnd` in
  `RealStandardIrreducibleCriterionReduction`, with `IsRealSwappable` in place of the
  hypotheses of Swap).
* `realInjectiveIntertwinerExists_moveList`: a list `X` whose blocks are swappable with every
  block of a list `Y` moves past `Y`:
  `RealInjectiveIntertwinerExists n (pre ++ X ++ Y ++ post) (pre ++ Y ++ X ++ post)`
  (induction on `X`: move the tail of `X` past `Y`, then the head).

## The reduction

`realUnlinkedSwapReduction : RealUnlinkedSwapReductionStatement`. Assume the four statements
and the hypotheses of Swap for `n`, `pre`, `post`, `x`, `y`. Let `X = realBlockExpand x` and
`Y = realBlockExpand y`.

1. `realRank (pre ++ X ++ Y ++ post) = n`, by `realRank_realBlockExpand`.
2. Every block of `X` is swappable with every block of `Y`: the blocks are nondegenerate,
   their real exponents are those of `x` and `y`, and they are unlinked because `x` and `y`
   are.
3. `realInjectiveIntertwinerExists_moveList` with the swaps of
   `realInjectiveIntertwinerExists_swap` gives
   `RealInjectiveIntertwinerExists n (pre ++ X ++ Y ++ post) (pre ++ Y ++ X ++ post)`.
4. Two uses of `realStandardModule_append_expand` on each side give
   `realStandardModule n (pre ++ X ++ Y ++ post) = realStandardModule n (pre ++ x :: y :: post)`
   and `realStandardModule n (pre ++ Y ++ X ++ post) = realStandardModule n (pre ++ y :: x :: post)`,
   and `RealInjectiveIntertwinerExists.of_eq` concludes.

So a weight-`0` block costs up to four swaps of nondegenerate blocks instead of one.

## Provenance

Derived. The four statements are Swap (`RealStandardIrreducibleCriterionReduction`) restricted
to blocks of fixed kinds; their sizes `2, 3, 3, 4` are Mœglin's reduction of Theorem 10b to
`GL(a)`, `a = 2, 3, 4` (p. 165), with character blocks as data `(1, s, σ)` and induction blocks
of nonzero weight as discrete series data `(2, s, D_p)` (§10, p. 164). The elimination of
weight-`0` induction blocks and the proof of the implication are internal to this module.

Source: C. Mœglin, Representations of GL(n) over the real field, in: T. N. Bailey and
A. W. Knapp (eds.), Representation Theory and Automorphic Forms, Proc. Sympos. Pure Math. 61
(1997), 157–166 (`bailey-knapp-1997-pspm61`; PDF page = printed page + 9). Proposition 7,
p. 162; §8, p. 163; §10, Theorem 10b and the data `(n_j, s_j, σ_j)`, p. 164; the reduction to
`GL(a)`, `a = 2, 3, 4`, p. 165.
