# Strict inversion growth for permutations ordered by lower-left corner counts

Authors: Worker 913 (Lean statement and this Markdown), Worker 308 (interface
design: the proposition is the combinatorial premise Worker 308 designed for the
boundary assembly).

`Langlands.GeneralLinear.UpperBruhatRankOrderInversionStatement` is a closed,
transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperBruhatRankOrderStatement`. It has no universe
parameters and no arguments. This module only states the proposition. It
contains no proof, and the proposition is not proved here.

## Exact proposition

```text
∀ (n : ℕ) (v w : Equiv.Perm (Fin n)), v ≠ w →
  (∀ i j : Fin (n + 1),
    UpperBruhatRank.count v i j.val ≤ UpperBruhatRank.count w i j.val) →
  permutationInversionCount n v < permutationInversionCount n w
```

The proposition quantifies over every natural number `n`, including `n = 0`,
and over every pair of permutations `v w` of `Fin n`. It has exactly two
premises:

1. `v ≠ w`;
2. for every `i j : Fin (n + 1)`, the count of `v` at `(i, j)` is at most the
   count of `w` at `(i, j)`.

The conclusion is the strict inequality of natural numbers
`permutationInversionCount n v < permutationInversionCount n w`. No other
premise occurs. There is no field, ring, coefficient or topology parameter. The
proposition is purely finite combinatorics of permutations.

## The two imported definitions

Both definitions are imported unchanged:
`Langlands.Group.GL.UpperBruhatRankProof` supplies the count, and
`Langlands.Group.GL.UpperBruhatFiltration` supplies the inversion count.

**The corner count.** `UpperBruhatRank.count w i k`, for
`w : Equiv.Perm (Fin n)`, `i : Fin (n + 1)` and `k : ℕ`, is

```text
(Finset.univ.filter fun c : Fin n => c.val < k ∧ i.val ≤ (w c).val).card
```

This is the number of columns `c` with `c.val < k` whose image `w c` satisfies
`i.val ≤ (w c).val`. The proposition always uses `k = j.val` for
`j : Fin (n + 1)`. In terms of the permutation matrix `permutation n K w`, whose
entry `(r, c)` is `1` exactly when `w c = r`, it counts the entries equal to `1`
in the lower-left block: rows `r` with `i.val ≤ r.val` and columns `c` with
`c.val < j.val`. The published lemma `UpperBruhatRank.rank_corner_permutation`
in the same module states, for every field `K`, that this count is the rank of
the zero-padded corner `UpperBruhatRank.corner i j` of `permutation n K w`.
The statement uses only the count, not ranks or matrices.

**Endpoints.** Both `i.val` and `j.val` range over `0, 1, …, n`. The row bound
is inclusive (`i.val ≤ (w c).val`). The column bound is exclusive
(`c.val < j.val`). From the definition, at the extreme endpoints the count does
not depend on the permutation. For `j.val = 0` and for `i.val = n` it is `0`.
For `i.val = 0` it is `j.val`. For `j.val = n` it is `n - i.val`, because `w` is
a bijection. Including these endpoints in the premise therefore adds no
constraint. They are kept so that the premise matches exactly the indexing
`i j : Fin (n + 1)` of the published rank characterization
`UpperBruhatRankCharacterizationStatement` in
`Langlands.Group.GL.UpperBruhatRankStatement`.

**The inversion count.** `permutationInversionCount n w` is
`relationInversions (fun a b : Fin n => b < a) (List.ofFn ⇑w)`. By the
published adapter `permutationInversionCount_eq_card`, it equals the number of
ordered pairs `(p₁, p₂) : Fin n × Fin n` with `p₁ < p₂` and `w p₂ < w p₁`.

## Direction of the inequalities

The premise says that `v` is dominated by `w`: each corner count of `v` is at
most the corresponding corner count of `w`. The conclusion says that the
dominated permutation `v` has strictly fewer inversions. In rank `2`, with `s`
the transposition of `0` and `1`, the count at `i.val = j.val = 1` is `0` for
the identity and `1` for `s`. Every other pair `(i, j)` is an endpoint, where
the two counts agree. So the premise holds for `v = 1, w = s`, and the
conclusion `0 < 1` holds too. The premise fails for `v = s, w = 1`.

This direction is the one needed for cell closures. If a point of the actual
cell `C_v = upperBruhatCell n K v` lies in the closure of `C_w`, then the
closedness of rank upper bounds and the rank characterization give
`count v i j.val ≤ count w i j.val` for all `i j`. This motivating deduction is
recorded in the published boundary proof. It is not part of this proposition.

## Provenance

This proposition is an internal auxiliary target. It is not quoted from any
source, and no literature is cited for it. It was isolated from the proof plan
for the published `UpperBruhatBoundaryStatement` in
`Langlands.Group.GL.UpperBruhatBoundaryStatement`. That statement is itself an
internal generalization motivated by Shalika's Lemma 1.7(2); see its Markdown.
In that plan, the topological argument reduces the boundary statement to this
finite comparison. Worker 308 designed the comparison as the sole premise of
the conditional assembly `upperBruhatBoundary_of_rankOrder` in
`Langlands.Group.GL.UpperBruhatBoundaryProof`, whose hypothesis `horder` is
written exactly as this proposition.

Mathematically, it is a form of the classical fact that comparing these rank
counts of permutations refines the comparison of their inversion counts. This
fact is related to the rank-matrix description of the Bruhat order on
permutations and to the strict growth of length along that order. The
proposition does not assume or mention either of these facts. It also does
not mention any Bruhat-order relation, orbit dimension, closure or rank
certificate.

## What the proposition does not assert

- It does not assert the converse. A strict inequality of inversion counts does
  not imply domination of the counts, and the proposition says nothing about
  that.
- It does not assert that domination of counts is a partial order, that it
  coincides with any Bruhat or closure order, or that the inversion counts
  differ by any particular amount.
- It makes no assertion about matrices, fields, cells, closures, topology or
  dimensions. Those appear above only as motivation.

## Status and reuse

The proposition is stated and not proved in this module. Separately, the
Library contains the published theorem
`Langlands.GeneralLinear.UpperBruhatBoundary.rankOrderInversion` in
`Langlands.Group.GL.UpperBruhatBoundaryProof`. Its stated type is the
proposition displayed above, written out verbatim. This module neither imports
nor uses that theorem. Recording it as a proof of this named statement is a
separate proof obligation.
