# Principal-series presentations of real standard modules with discrete-series blocks

Lean module: `Langlands.Representation.Archimedean.RealDiscretePresentation`. Author: Worker
380, for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), as part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). `MoeglinDatum.IsLinked.symm` and `AreRealBlocksUnlinked.symm`
are in `Langlands.Archimedean`; all other declarations are in
`Langlands.Archimedean.RealDiscretePresentation`.

## Purpose and provenance

The module proves no statement of record. For a list `Ds = [D₁, …, D_r]` of induction data of
nonzero weight and a list `M` of real blocks, it builds a surjective `(𝔤, K)`-intertwiner from
the principal series of

`sourceList Ds M = x(D₁), …, x(D_r), M, y(D_r), …, y(D₁)`

onto the standard module of `targetList Ds M = M, D_r, …, D₁`. For `D` of weight `±ℓ`
(`ℓ > 0`) and exponent `t`, `x(D)` is the character `|·|^{t − ℓ/2}` and `y(D)` is
`sgn^{ℓ+1} |·|^{t + ℓ/2}`. The map is a composite of two kinds of Library maps.

* The tail maps of `RealInducedCharacterMaps` (Library): the principal series of
  `[x(D), y(D)]` maps onto the induction block `D` (the discrete series `D_ℓ` twisted by
  `|det|^t` is a quotient of this principal series).
* Swaps of adjacent unlinked blocks: `realUnlinkedSwap` (Library,
  `RealLinkedLanglandsQuotientNotLargeProof`) gives an injective intertwiner when the first
  block has the larger or equal real exponent, and `realSwapInjectiveIntertwinerSurjective`
  (Library, `RealSwapSurjectiveProof`) shows that it is also surjective.

All declarations are internal. Unlinkedness is Mœglin's condition `MoeglinDatum.IsLinked`
(Library, `RealLargeStandardIrreducibleReduction`; Mœglin 1997, Theorem 10b).

## Notation

* `KF n ds`: the `O(n)`-finite vectors of `realStandardModule n ds`.
* `IsGKMap n ds es q`: `q` commutes with `O(n)` and with the Lie algebra action
  (`InductionStages.IsRealStandardIntertwiner`).
* `HasGKSurjection n ds es`: there is a surjective linear `q : KF n ds → KF n es` with
  `IsGKMap n ds es q`. It is reflexive (`refl`, `of_eq`) and transitive (`trans`).

## Declarations

* `MoeglinDatum.IsLinked.symm`, `AreRealBlocksUnlinked.symm`: linkage is symmetric. Proof: case
  analysis on the two data; for two characters replace the integer `k` by `−k`.
* `isGKMap_symm`, `HasGKSurjection.of_bijective_symm`: the inverse of a bijective
  `(𝔤, K)`-intertwiner is one, so a bijective intertwiner gives a surjection in the reverse
  direction.
* `exists_bijective_swap`: if `x, y` are unlinked and `Re(y) ≤ Re(x)` (real exponents), the
  Library swap intertwiner `pre ++ x :: y :: post → pre ++ y :: x :: post` is bijective.
* `hasGKSurjection_swap`: for unlinked `x, y` the swap surjection exists in either order of the
  real exponents. If `Re(y) ≤ Re(x)` use `exists_bijective_swap`; otherwise invert the bijective
  swap in the other direction.
* `hasGKSurjection_move`: a block `x` unlinked with every block of `zs` moves past `zs`
  (induction on `zs`, one swap at a time, inside arbitrary `pre` and `post`).
* `ySign d = (|d.weight| + 1) mod 2`; `xBlock d = character (cb d 0)` and
  `yBlock d = character (ca d (ySign d))`, with the Library characters `cb`, `ca` of
  `RealInducedCharacterMaps` (exponents `t − |m|/2` and `t + |m|/2`).
* `hasGKSurjection_tail`: for `0 < |d.weight|`, the principal series of
  `pre ++ [x(d), y(d)] ++ post` maps onto the standard module of
  `pre ++ [induced d] ++ post`. Proof: the Library tail map
  `RealInducedCharacter.tail_surjective` is surjective, and
  `RealInducedCharacter.modulo_tail` with
  `RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot` shows that it is a
  `(𝔤, K)`-intertwiner. The sign condition of these lemmas is
  `ySign d + 0 ≡ |d.weight| + 1 (mod 2)`.
* `hasGKSurjection_chain` (**presentation**). Suppose `0 < |D.weight|` for all `D ∈ Ds`, every
  `x(D)` is unlinked with every block of `M`, and `x(D)` is unlinked with the block `D'` for
  every pair `D` before `D'` in `Ds`. Then
  `HasGKSurjection n (pre ++ sourceList Ds M ++ post) (pre ++ targetList Ds M ++ post)` when
  the left side has rank `n`.

  Proof by induction on `Ds = d :: Ds'`. The induction hypothesis, applied inside
  `pre ++ [x(d)]` and `[y(d)] ++ post`, maps onto
  `pre ++ x(d) :: (targetList Ds' M ++ y(d) :: post)`. Then `x(d)` moves to the right past
  `targetList Ds' M = M ++ Ds'.reverse.map induced` (`hasGKSurjection_move`; the hypotheses
  give the unlinkedness). Finally the tail map of `d` replaces the adjacent pair
  `x(d), y(d)` by `induced d`, which gives `pre ++ targetList (d :: Ds') M ++ post`.
