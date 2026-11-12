# Complete tuples of points of an étale chart

This module supplies the combinatorial input of the weak Chow construction (Stacks
Project, Tag 089I): tuples of points of an étale chart `W` of an algebraic space `X`
that contain every point of their fibre.

## Fibre bound

`exists_fibre_card_le`: let `S` be affine, `X` a quasi-separated algebraic space over
`S`, and `a : h_V → X` étale with `V` affine. There is `D : ℕ` such that for every
field `L`, every `s₀ : Spec L → S`, every `s : Spec L → V` over `S`, and every
injective family `v : ι → (Spec L → V)` of points over `S` with
`a ∘ v i = a ∘ s` for all `i`, the family has at most `D` members.

The proof follows the library proof of
`EtaleChartFibreCount.exists_fibre_card_le` (stated there over a field base) with
points `Over.mk s₀ ⟶ V` over the general affine base. The self-fibre product
`V ×_X V` is quasi-compact (`compactSpace_selfPullback`, using that `X` is
quasi-separated and `V ×_S V` is affine), so it is covered by finitely many affine
opens. The second projection `V ×_X V → V` is étale, and on each affine open
`exists_card_le_of_etale_affine` bounds the number of `L`-points over a fixed point
of `V`. The points `(v i, s)` of `V ×_X V` are pairwise distinct; sorting them by an
affine open containing their image gives the bound `∑ D_W`.

## Complete locus

Let `π : h_W → X` be relatively representable and `P` a fibre power
`W ×_X ⋯ ×_X W` with `n + 1` factors (`ChartFibrePower π (Fin (n + 1))`), with
projections `P.pr i`. `succ ha P` is the fibre power with `n + 2` factors
`W ×_X P`, with new coordinate `succFst` and projection `succSnd` to `P`.

- `completeLocus ha P`: the set of points `t` of `P` such that every point `t'` of
  `W ×_X P` over `t` has its new coordinate equal to one of the old ones, in the sense
  of `EqAt` (equality of the two morphisms from `Spec κ(t')`).
- `exists_eqAt_of_mem_completeLocus`: if `h : T ⟶ P` and `w : T ⟶ W` (over `S`) have
  `π ∘ w = π ∘ pr₀ ∘ h`, then at every point `τ` of `T` with `h τ` complete, `w`
  agrees with some `pr_i ∘ h` at `τ`. Proof: lift `(w, h)` to `W ×_X P` and apply the
  definition of completeness at the image of `τ`; `eqAt_comp_iff` transports the
  agreement back to `τ`.

## Existence of complete points

- `coincidences P t`: the set of pairs `(i, j)` with `i ≠ j` at which the coordinates
  `pr_i` and `pr_j` agree at `t`.
- `exists_coincidences_lt`: suppose every injective family of points over a field
  with a common image in `X` has at most `D` members, and `D < n + 2`. If `t` is not
  complete, there is `t''` with the same first coordinate as `t` and strictly fewer
  coincidences. Proof: take `t'` over `t` whose new coordinate differs from all old
  ones. If `t` had no coincidences, the `n + 2` coordinates of `t'` would be pairwise
  distinct points over `κ(t')` with a common image in `X`, contradicting the bound.
  Otherwise choose a coincidence `(j, k)` with `k ≠ 0`, and let `t''` be the image of
  `t'` under the map that replaces coordinate `k` by the new coordinate
  (`mapIndex` with `σ c = if c = k then 0 else c.succ`). Every coincidence of `t''`
  is one of `t` (the new coordinate agrees with no old one), and `(j, k)` is lost.
- `exists_mem_completeLocus_of_bound`: under the same bound, every point `w` of `W` is
  the first coordinate of a complete point. Proof: start from the diagonal point
  `(w, …, w)` and induct on the number of coincidences.
- `exists_completeLocus`: if `S` and `W` are affine, `X` is quasi-separated and `π` is
  étale, then for some `n` every point of `W` is the first coordinate of a complete
  point of `ChartFibrePower.fin hπ.1 n` (take `n = D` from `exists_fibre_card_le`).

## Provenance

The complete locus is the set `G` of the proof of Stacks Lemma 089I, whose points
correspond to tuples listing all points of a fibre. Stacks works with strata of
pairwise distinct tuples of each length; this formalization uses tuples of a single
length `n + 1` with repetitions allowed, which is why existence is proved by
minimizing the number of coincidences.
