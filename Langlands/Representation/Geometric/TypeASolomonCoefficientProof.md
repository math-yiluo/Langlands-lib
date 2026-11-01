# Proof of the signed type-A Solomon coefficient identity

Author: Worker 379.

`Langlands.Geometric.typeASolomonCoefficientStatement` proves exactly
`Langlands.Geometric.TypeASolomonCoefficientStatement`: for every natural rank
`n` and all `B K : BlockShape n` with `blockWeyl K ≤ blockWeyl B`,

```text
∑_C (-1)^(n - C.length) · #{w ∈ MinimalRepresentatives B C |
      blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w) = blockWeyl K}
  = (-1)^(n - K.length).
```

The proof is a finite combinatorial argument on permutations of `Fin n` and on
sets of interior cuts. It has no hypotheses beyond those of the proposition. The
sum over `C` uses the statement's own `Fintype.ofFinite` structure, which the
proof introduces as a local instance. The helper declarations live in the
namespace `Langlands.Geometric.TypeASolomon`.

## Edges and the two order conditions

An interior edge `e : Fin (n - 1)` joins the coordinates `edgeLo e = e.val` and
`edgeHi e = e.val + 1` of `Fin n`. By the public cut-side law
`blockIndex_eq_iff_cut_sides`, the endpoints of `e` lie in one block of a shape
`B` exactly when `e ∉ B.cuts` (`blockIndex_lo_eq_hi_iff`).

`SourceIncreasing B w` says that `w` is strictly increasing on every block of
`B`. By definition, `IsMinimalRepresentative B C w` is
`SourceIncreasing B w ∧ SourceIncreasing C w.symm`. The public
`strictMono_blocks_iff_descents` turns the second condition into
`permutationDescents w.symm ⊆ C.cuts` (`inverseIncreasing_iff`). Two further
facts are used throughout: a source-increasing permutation increases along
any two coordinates of one block (`lt_of_sameBlock`), and blocks are intervals
(`blockIndex_eq_of_between`, from `blockIndex_monotone`).

## The subgroup equality as a relation on coordinates

`intersection_eq_iff` shows that the actual subgroup equality
`blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w).toMonoidHom = blockWeyl K`
holds exactly when, for all coordinates `a` and `b`,

```text
blockIndex K a = blockIndex K b  ↔
  blockIndex B a = blockIndex B b ∧ blockIndex C (w a) = blockIndex C (w b).
```

A permutation `u` lies in the comap exactly when
`blockIndex C (w (u x)) = blockIndex C (w x)` for every `x`
(`mem_comap_conj_iff`), since `MulAut.conj w u = w * u * w⁻¹`. The
orientation is therefore the source-side intersection `W_B ∩ w⁻¹ W_C w`. From
the subgroup equality, membership of the transposition `Equiv.swap a b` on both
sides gives the relation, because a transposition preserves the blocks of a
shape exactly when it swaps two coordinates of one block
(`swap_mem_blockWeyl_iff`). Conversely, the relation, applied to `u x` and `x`,
gives equal membership for every permutation `u`.

## Admissible cut sets

For a fixed permutation `w` and a set `S` of interior edges, `Admissible B K w S`
means:

1. `w` is `SourceIncreasing B w`;
2. every inverse descent of `w` lies in `S`;
3. for every edge `i ∉ B.cuts`, `i ∈ K.cuts` holds exactly when every edge `e`
   with `e.val = w (edgeLo i)` and `e.val + 1 = w (edgeHi i)` lies in `S`.

In clause 3 there is at most one such `e`, and it exists exactly when the images
of the endpoints of `i` are adjacent.

`admissible_iff` proves, under `B.cuts ⊆ K.cuts`, that

```text
IsMinimalRepresentative B C w ∧ (intersection = blockWeyl K)
  ↔ Admissible B K w C.cuts.
```

The key step is `not_sameBlock_iff`. Let `w` be increasing on the blocks of
`B` and `w⁻¹` increasing on the blocks of `C`, and let `i ∉ B.cuts`. Then
`w (edgeLo i) < w (edgeHi i)`. These images lie in different blocks of `C`
exactly when the condition of clause 3 holds for `S = C.cuts`. If the images
are adjacent, this is the edge law. If they are not adjacent, a coordinate `z`
lies strictly between them. Equal `C`-blocks would put `z` in the same block,
and then `w⁻¹` would map `z` strictly between `edgeLo i` and `edgeHi i`, which
is impossible. Hence the images always lie in different blocks.

The forward direction of `admissible_iff` applies the coordinate relation to
the endpoints of each edge `i ∉ B.cuts`. For the backward direction it suffices
to treat `a ≤ b`:

- If `a` and `b` lie in one block of `K`, they lie in one block of `B` by the
  cut inclusion. Suppose that `w a` and `w b` lay in different blocks of `C`.
  Then some cut `c` of `C` separates them. A discrete intermediate-value step
  (`exists_step`) finds consecutive coordinates `i` and `i + 1` in `[a, b]`
  whose images are separated by `c`. The edge `i` is not a cut of `K`, hence
  not a cut of `B`, so clause 3 and `not_sameBlock_iff` put its images in one
  block of `C`. This is a contradiction.
- Suppose `a` and `b` lie in one block of `B` and their images lie in one block
  of `C`, but some cut `e` of `K` lies between them. Then `e` is not a cut of
  `B`, so clause 3 puts the images of its endpoints in different blocks of `C`.
  However, `w` is monotone on the `B`-block containing `a`, `e`, `e + 1` and
  `b`, and `blockIndex C` is monotone, so both images are squeezed into the
  common `C`-block of `w a` and `w b`. This is a contradiction.

## Reindexing the signed sum

`natCard_eq_sum` rewrites the cardinality of the nested subtype of
`MinimalRepresentatives B C` as the number of permutations satisfying both
conditions, that is, as `∑_w [Admissible B K w C.cuts]`. The public
`sign_eq_pow_uncuts_card` rewrites the sign `(-1)^(n - C.length)` as
`(-1)^(card C.cutsᶜ)`. After exchanging the two finite sums, the public
bijection `BlockShape.cutEquiv n : BlockShape n ≃ Finset (Fin (n - 1))`
replaces the sum over shapes `C` by the sum over all cut sets `S`. The integer
to compute is therefore

```text
∑_w ∑_S [Admissible B K w S] · (-1)^(card Sᶜ).
```

## Cancellation for permutations with a free edge

Call an edge `e₀` free for `w` if it is not an inverse descent of `w` and it
is not `w (edgeLo i)` for an edge `i ∉ B.cuts` with adjacent images. The
admissibility conditions never mention a free edge. Toggling it, via
`S ↦ symmDiff S {e₀}`, therefore preserves admissibility and changes the
parity of `card Sᶜ`. `Finset.sum_ninvolution` then shows that the inner sum
vanishes (`sum_eq_zero_of_free`). The inner sum also vanishes when `w` is not
source-increasing, because then no `S` is admissible. This cancellation
toggles one edge of an explicit predicate. It does not restate Mathlib's
Boolean identity `Finset.sum_powerset_neg_one_pow_card`.

## The block reversal

The block reversal is
`reversal B = (Tuple.sort (reversalKey B)).symm`. Here `reversalKey B a` is the
lexicographic pair consisting of the block of `a` in reversed order and then
`a` itself. The reversal lists the blocks of `B` from last to first and keeps
each block increasing. It is source-increasing (`reversal_sourceIncreasing`).
It sends every edge `i ∉ B.cuts` to an adjacent pair (`reversal_adjacent`), and
it has no free edge (`reversal_no_free`): an edge whose preimages lie in
different blocks is an inverse descent, and an edge whose preimages lie in one
block is the image of an edge inside that block.

Conversely, `eq_reversal` shows that every source-increasing permutation `w`
without free edges equals `reversal B`. On each edge `e`, the composite
`reversalKey B ∘ w⁻¹` is monotone. If `e` is an inverse descent, the
source-increasing condition forces its preimages into different blocks, in
decreasing block order. Otherwise `e` is the image of an edge inside one block.
Monotonicity on edges gives monotonicity on `Fin n` (`monotone_of_adjacent`).
Since the key is injective, `Tuple.eq_sort_iff` identifies `w⁻¹` with the
sorting permutation. Hence every permutation other than `reversal B` contributes
zero, and `Finset.sum_eq_single` keeps only the reversal term.

## The surviving term

For `w = reversal B`, let `T` be the set of edges `w (edgeLo i)` for edges
`i ∉ K.cuts`. These images are adjacent pairs, because `B.cuts ⊆ K.cuts` and
`reversal_adjacent`. `sum_reversal` shows that `Tᶜ` is the unique admissible
cut set. Edges of `T` must be omitted by clause 3. Every other edge is an
inverse descent or the image of a `K`-cut inside a block of `B`, so it must be
included. `Tᶜ` itself satisfies all three clauses. The map `i ↦ w (edgeLo i)` is
a bijection from `K.uncuts` onto `T` (`Finset.card_bij`), so the surviving term
is `(-1)^(card K.uncuts)`. By `sign_eq_pow_uncuts_card`, this equals
`(-1)^(n - K.length)`.

## Small ranks

No case distinction on `n` is made beyond the internal monotonicity helper.
When `n` is `0` or `1`, the edge type `Fin (n - 1)` is empty. All edge
conditions are then vacuous, there is exactly one cut set and hence exactly one
shape, and every argument above applies unchanged. In rank `0` the only
permutation of `Fin 0` is the reversal. The helper `monotone_of_adjacent` treats
`n = 0` by elimination on `Fin 0` and `n = m + 1` by
`Fin.monotone_iff_le_succ`.

## Provenance and dependencies

Aubert (1995) quotes the identity after equation (1.8), on p. 2182, citing
Solomon through Carter 2.7.7. The proposition is the type-A form of that
identity for block Weyl intersections; its Markdown gives the source
dictionary. This module does not translate the cited proof. It is an internal
finite proof that pairs target cut sets by toggling and identifies the block
reversal as the unique surviving permutation. It proves no geometric lemma,
Aubert compatibility, involution, irreducibility or classification statement.

The project imports are the statement module and the public combinatorial
modules `Geometric.BlockWeylCutProof` (cut sides and
`blockWeyl_le_iff_cuts_subset`), `Geometric.BlockShapeCutCounts`
(`sign_eq_pow_uncuts_card`, `BlockShape.uncuts`) and
`Geometric.PermutationDescents` (descents and `strictMono_blocks_iff_descents`).
These modules transitively provide `Geometric.BlockShapeCuts`
(`BlockShape.cutEquiv`), `Geometric.WeylUniquenessProof` and
`Geometric.WeylMinimalRepresentativeProof`. The import closure contains no
representation-theoretic proof, classification or exhaustion result.

The local `swap_mem_blockWeyl_iff` restates
`Langlands.CuspidalSupport.swap_mem_blockWeyl_iff` from
`CuspidalSupport.MinimalWeylTransportProof`. It is kept local because that
module imports representation-theoretic transport modules, which this purely
combinatorial proof avoids.
