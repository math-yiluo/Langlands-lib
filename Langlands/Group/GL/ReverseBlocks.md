# Reversal of standard block geometry

Author: Worker 76.

This pair constructs a reversed shape and an actual permutation matrix that
exchange the upper and lower standard block radicals in both orientations.
It imports the published `Langlands.Group.GL.OppositeBlocks` and
`Langlands.Group.GL.Maps` modules, and uses the original `BlockShape`,
`parabolic`, `oppositeParabolic`, `unipotentSubgroup`, and
`oppositeUnipotentSubgroup` without changing their definitions.

## Construction and conventions

For `B : BlockShape n`, `B.reverse` has the same number of blocks and size
`B.size i.rev` at position `i`. Positivity follows from `B.positive`, and
`Equiv.sum_comp` for `Fin.revPerm` proves that the total rank remains `n`.
The standard consecutive coordinate numbering is the existing `indexEquiv`
of this new shape.

`B.reverseIndexEquiv` sends the reversed shape's dependent coordinate
`(i,a)` to the original shape's coordinate `(i.rev,a)`.
`B.reversePermutation` composes this equivalence with the two standard
coordinate equivalences, giving a permutation of `Fin n`.
`B.reverseMatrix R` is its actual permutation matrix unit, constructed by
`GeneralLinear.permutation`. In particular,

```
reversePermutation (B.reverse.index i a) = B.index i.rev a.
```

This permutation reverses the order of whole blocks and preserves the order
of positions within each block. It is not asserted to be the full antidiagonal
permutation or to be involutive. For example, with original sizes `(1,2)`,
its images of the three reversed-shape standard positions are `(1,2,0)`.
Both requested conjugacy orientations use this same matrix and are proved
directly, with no surjectivity assumption on the operation `B ↦ B.reverse`.

## Entry calculations and subgroup equalities

`reverseMatrix_conjugate_entry` applies the published
`permutation_conjugate_entry`. The entry of `w*g*w⁻¹` at original coordinates
`(i.rev,a)` and `(j.rev,b)` is the entry of `g` at reversed-shape coordinates
`(i,a)` and `(j,b)`.

The two parabolic membership equivalences follow by substituting that entry
formula into the published upper and lower zero conditions. The inequality
`i < j` becomes `j.rev < i.rev`; `Fin.rev_surjective` covers every original
block index in the converse direction. The private diagonal equivalence
uses the same entry formula and preserves the Kronecker delta, since inner
coordinates do not change.

Combining these facts with the published radical membership descriptions
proves both radical membership equivalences. `Subgroup.mem_map_equiv` then
turns them into the exported subgroup equalities, where
`w = B.reverseMatrix R`:

- `reverse_unipotentSubgroup_map_conj` states that the image of
  `B.reverse.unipotentSubgroup R` under `MulAut.conj w` is
  `B.oppositeUnipotentSubgroup R`.
- `reverse_oppositeUnipotentSubgroup_map_conj` states that the image of
  `B.reverse.oppositeUnipotentSubgroup R` under `MulAut.conj w` is
  `B.unipotentSubgroup R`.

These are equalities of actual subgroups of `Langlands.GeneralLinear n R`,
not abstract isomorphisms of replacement groups.

## Properness and scope

`inverseTranspose_mem_oppositeParabolic_iff` proves that the published
inverse transpose sends a matrix into the original lower parabolic exactly
when that matrix belongs to the original upper parabolic. Its proof swaps
row and column indices in the zero conditions and uses inverse closure of
the upper subgroup.

Surjectivity of inverse transpose proves `oppositeParabolic_eq_top_iff`.
Surjectivity of conjugation and the reversed upper-to-lower membership
lemma then prove `reverse_parabolic_eq_top_iff`. Negating this equivalence
gives `reverse_parabolic_ne_top_iff`:

```
B.reverse.parabolic R ≠ ⊤ ↔ B.parabolic R ≠ ⊤.
```

All constructions and lemmas quantify over every natural rank `n` and every
commutative ring `R` in an arbitrary universe. There is no nonempty-block,
positive-rank, field, nontrivial-ring, or properness hypothesis. Hence they
include the empty shape at rank zero, one-block shapes, all longer positive
block lists, and every field required by the task. The proofs never choose
a block or an inner coordinate; universal entry conditions and finite
bijections also apply when the index types are empty.

## Derived provenance

This is an internal finite combinatorial consequence of the published block
and matrix constructions. The source conventions for those constructions
are documented in `Blocks.md`, `OppositeBlocks.md`, and `Maps.md`. This pair
adds no independent claim about the original literature. Its new content is
the reversed finite size list, the explicit coordinate permutation, and the
intrinsic subgroup/properness correctness laws described above. The proof
uses only the imported entry characterizations, finite reversal, subgroup
membership, and the already constructed inverse-transpose automorphism.
No analytic, representation-theoretic, or classification premise is used.
