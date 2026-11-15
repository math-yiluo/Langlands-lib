# Reducing Speh's irreducibility criterion ("if" part) for `GL_n(ℝ)` to unlinked swaps

Lean module: `Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction`.

The Library statement `Langlands.Archimedean.RealStandardIrreducibleCriterionStatement` (Sp,
module `RealLargeStandardIrreducibleReduction`) is the "if" direction of Speh's criterion,
Mœglin 1997, Theorem 10b (printed p. 164), for Langlands-ordered lists: if `ds` is a list of
real blocks with `realRank ds = n`, `IsRealLanglandsOrdered ds` and
`IsRealMoeglinUnlinked ds`, then the standard module of `ds` is an irreducible
`(𝔤, K)`-module.

This module states two new statements, Swap and Rev below, and proves that they imply Sp
together with the Library's Langlands-quotient statement `RealStandardLanglandsQuotientStatement`
(L). The implication is `realStandardIrreducibleCriterionReduction`. It adds no hypothesis to
Sp. Swap and Rev are only stated here; they still need proofs.

Notation as in `RealLargeStandardIrreducibleReduction.md`: for a list `ds` of real blocks,
`I(ds)` is the `(𝔤𝔩_n(ℝ), O(n))`-module `(realStandardRep n ds, realStandardLie n ds)` on the
`O(n)`-finite functions `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`.
That Markdown explains why `I(ds)` is Mœglin's `I(χ)` for `χ = realMoeglinData ds`, induced
from the parabolic subgroup with the blocks of `ds` in the given order along the diagonal.
An intertwiner `T : I(ds) → I(es)` is a `ℂ`-linear map `T` with
`IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T`: it commutes
with the actions of `O(n)` and of `𝔤𝔩_n(ℝ)` (`RealGenericParameterReduction.lean`).

## Unlinked blocks

`AreRealBlocksUnlinked x y` says that no Mœglin datum of the block `x` is linked to a Mœglin
datum of the block `y`:
`∀ a ∈ realBlockMoeglinData x, ∀ b ∈ realBlockMoeglinData y, ¬ a.IsLinked b`.
`MoeglinDatum.IsLinked` and `realBlockMoeglinData` are the Library's transcriptions of the
conditions of Theorem 10b and of the data of a block (`RealLargeStandardIrreducibleReduction.md`).
The data of a single block are never linked to each other: a block has one datum, or two
character data with the same exponent, and linking needs a nonzero difference of exponents.
So Theorem 10b for the list `[x, y]` says that the module `I([x, y])` of
`GL_{r_x + r_y}(ℝ)` is irreducible if and only if `AreRealBlocksUnlinked x y`
(`IsLinked` is symmetric).

## The two statements

1. `RealUnlinkedSwapStatement` (Swap). Let `pre`, `post` be lists of real blocks and `x`, `y`
   real blocks with `realRank (pre ++ x :: y :: post) = n`,
   `realBlockExponent y ≤ realBlockExponent x` and `AreRealBlocksUnlinked x y`. Then there is
   an injective intertwiner `T : I(pre ++ x :: y :: post) → I(pre ++ y :: x :: post)`.

   Source and why it is true. This is the rank-one step of Mœglin's proof of Theorem 10b. In
   §8 (printed p. 163) she normalizes the intertwining operators `A(w, χ_s) : I(χ_s) →
   I(wχ_s)` of §5 (Theorem 5, p. 160) to `A'(w, χ_s)`, holomorphic and nonzero for positive
   `s`. Exchanging two adjacent unlinked blocks gives a bijective operator: for two
   characters by the `GL_2` computation (Proposition 7 (ii), (iii), p. 162), and for blocks
   through the reduction of Theorem 10b to `GL(a)`, `a = 2, 3, 4`, whose cases Speh
   computed (p. 165). Equivalently: by Theorem 10b for `[x, y]` the module
   `I([x, y])` is irreducible, so `I([y, x])`, which has the same composition factors, is
   isomorphic to it; induction in stages from the Levi subgroup
   `GL_{r_pre} × GL_{r_x + r_y} × GL_{r_post}` then gives an isomorphism
   `I(pre ++ x :: y :: post) ≅ I(pre ++ y :: x :: post)`. Swap asks only for an injective
   intertwiner, and only when `Re t(y) ≤ Re t(x)`: this is the direction, from the positive
   order to the exchanged one, in which Mœglin's normalized operators are holomorphic and
   nonzero (§8). The lists `pre` and `post` are arbitrary; they need
   not be in Langlands order.

2. `RealReverseIntertwinerKernelStatement` (Rev). Let `ds` be a list of real blocks with
   `realRank ds = n` and `IsRealLanglandsOrdered ds`. Let `T : I(ds) → I(ds.reverse)` be any
   intertwiner and `W` any `(𝔤, K)`-submodule of `I(ds)` (`IsGKSubmodule`) with `W ≠ ⊤`. Then
   `W ≤ ker T`.

   Source and why it is true. Mœglin's Theorem 4 (p. 159, the special case of Langlands'
   theorem; Theorem 10a, p. 164, for blocks; she refers to Knapp 1986, Theorems 8.54 and 7.24
   and Proposition 8.61): for positive `χ`, (i) `I(χ)` has a unique irreducible quotient
   `J(χ)`, and `I(w₀χ)` has a unique irreducible submodule, isomorphic to `J(χ)`; (ii) `J(χ)`
   occurs with multiplicity one as a subquotient of `I(χ)`. Here `I(ds.reverse)` is `I(w₀χ)`:
   reversing the blocks is the action of the longest Weyl element on the Levi data. Inside a
   group of blocks with equal real exponents the order does not matter, since the induced
   module from such a group is an irreducible tempered module up to a twist (Proposition 3,
   p. 159, for characters; §6, p. 160, for discrete series blocks: for `GL(n)`, induction
   from a discrete series with imaginary parameter is irreducible); this also covers the two data of a weight-`0` block, which keep their order in
   `ds.reverse`. Knapp 1986 realizes `J(χ)` as the image of the long intertwining operator
   `A(S̄ : S : ω : ν)` (§VIII.15, pp. 266–267, Theorem 8.54) inside the module induced from
   the opposite parabolic, which is `I(ds.reverse)` after conjugation by `w₀`.

   Derivation of Rev, using also that standard modules have finite length. Let `R` be the
   largest proper submodule of `I(ds)` (so `I(ds)/R ≅ J`). If `T = 0`, then `W ≤ ker T`
   trivially. Otherwise the image of `T` is a nonzero submodule of `I(ds.reverse)`, so it
   contains the unique irreducible submodule `J`; and `ker T ⊆ R`. If `ker T ≠ R`, then
   `R / ker T` is a nonzero submodule of `I(ds)/ker T ≅ im T ⊆ I(ds.reverse)`, so it also
   contains a copy of `J`; then `J` occurs twice in `I(ds)` (in `R / ker T` and as
   `I(ds)/R`), against (ii). So `ker T = R ⊇ W`.

The proof of Sp from these statements does not need any identification of `I(ds)` with
Mœglin's module. Proofs of Swap and Rev do: they must identify `realStandardModule n ds`
with `I(χ)` as described in `RealLargeStandardIrreducibleReduction.md`, and they need
intertwining operators, finite length and Langlands' theorem for `GL_n(ℝ)`, none of which
is in the Library yet.

## The reduction

`RealStandardIrreducibleCriterionReductionStatement` is the implication L → Swap → Rev → Sp.
The theorem `realStandardIrreducibleCriterionReduction` proves it.

Proved helpers:

* `IsRealStandardIntertwiner.comp_standard`: the composite of intertwiners
  `I(ds) → I(es) → I(fs)` is an intertwiner. It uses the two clauses of
  `IsRealStandardIntertwiner` of the first map and `map_realStandardRep`,
  `map_realStandardLie` for the second.
* `RealInjectiveIntertwinerExists n ds es`: the proposition that an injective intertwiner
  `I(ds) → I(es)` exists. It is an internal abbreviation. It is reflexive (`refl`, via the
  identity and `isRealStandardIntertwiner_id`) and transitive (`trans`, via
  `comp_standard`).
* `realRank_perm`: permuting the blocks does not change `realRank`.
* `realInjectiveIntertwinerExists_moveToEnd`: if every block `b` of a list `l` has
  `Re t(b) ≤ Re t(a)` and is unlinked from `a`, then
  `RealInjectiveIntertwinerExists n (pre ++ a :: l ++ post) (pre ++ l ++ a :: post)`. By
  induction on `l`: one Swap moves `a` past the first block of `l`, and the rest follows
  with `pre ++ [b]` in place of `pre`. The rank hypothesis is transported with
  `realRank_perm`.
* `realInjectiveIntertwinerExists_reverse`: if `l` is pairwise (in list order) of
  non-increasing real exponent and unlinked, then
  `RealInjectiveIntertwinerExists n (pre ++ l ++ post) (pre ++ l.reverse ++ post)`. By
  induction on `l`: move the head to the end of `l`, then reverse the tail.
* `pairwise_exponent_unlinked`: for `ds` Langlands-ordered and `IsRealMoeglinUnlinked`,
  `ds` is pairwise of non-increasing real exponent and unlinked. `IsRealMoeglinUnlinked ds`
  is pairwise non-linking of `realMoeglinData ds = ds.flatMap realBlockMoeglinData`, so
  `List.pairwise_flatMap` gives non-linking between the data of any two blocks in order.

Proof of the reduction. Assume L, Swap, Rev and the hypotheses of Sp for `n` and `ds`.

1. L gives a proper submodule `R ≠ ⊤` of `I(ds)`, so `I(ds)` has an element outside `R`;
   it is nonzero, so `I(ds)` is nontrivial. This is the only use of L.
2. `pairwise_exponent_unlinked` and `realInjectiveIntertwinerExists_reverse` with empty
   `pre` and `post` give an injective intertwiner `T : I(ds) → I(ds.reverse)`.
3. Let `W` be a `(𝔤, K)`-submodule. If `W = ⊤` we are done. Otherwise Rev gives
   `W ≤ ker T = ⊥`, so `W = ⊥`.

This is Mœglin's argument in §8 (p. 163): "they imply that `A'(w, χ_{s₀})` gives an
isomorphism between `I(χ_{s₀})` and `I(w₀χ_{s₀})` and the Langlands theorem then gives an
isomorphism with `J(χ_{s₀})`, which is irreducible by definition". The reduction needs only
an injective map, composed from adjacent swaps, and replaces "isomorphic to `J`" by Rev.

## Provenance

Derived. `AreRealBlocksUnlinked` restricts Mœglin's pairwise condition of Theorem 10b
(through the Library's `MoeglinDatum.IsLinked`) to the data of two blocks. Swap is the
bijectivity of Mœglin's normalized intertwining operator for an adjacent exchange of
unlinked blocks (§§5, 7, 8 and the reduction to `GL(2)`, `GL(3)`, `GL(4)` on p. 165),
weakened to the existence of an injective intertwiner when `Re t(y) ≤ Re t(x)`. Rev is a
consequence of Langlands' theorem (Mœglin's Theorem 4 (i) and (ii), Theorem 10a; Knapp 1986,
Theorem 8.54, Proposition 8.61) and finite length, derived above. The split of Sp into L,
Swap and Rev and the proof of the implication are internal to this module; the route is
Mœglin's proof of Theorem 1 in §8, extended to blocks as she indicates for Theorem 10b.

Sources:

* C. Mœglin, Representations of GL(n) over the real field, in: T. N. Bailey and
  A. W. Knapp (eds.), Representation Theory and Automorphic Forms, Proc. Sympos. Pure
  Math. 61 (1997), 157–166 (`bailey-knapp-1997-pspm61`; PDF page = printed page + 9).
  Proposition 3 and Theorem 4, p. 159; §5 and Theorem 5, pp. 159–160; §6, p. 160;
  Proposition 7,
  p. 162; §8, p. 163; §10, Theorems 10a and 10b, p. 164; the reduction to `GL(2)`,
  `GL(3)`, `GL(4)`, p. 165.
* A. W. Knapp, Representation Theory of Semisimple Groups: An Overview Based on Examples,
  Princeton University Press, 1986 (Library source
  `provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855`; PDF page =
  printed page + 14). §VIII.15, the Langlands quotient as the image of
  `A(S̄ : S : ω : ν)`, pp. 266–267, Theorem 8.54, p. 267; Proposition 8.61, p. 274;
  Theorem 7.24, p. 200.
