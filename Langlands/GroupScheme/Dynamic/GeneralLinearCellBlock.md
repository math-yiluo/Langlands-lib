# A block lemma for the opposite cell of `GL_n`

This internal unit proves a vanishing statement for the parabolic factor of a product in the
opposite cell of a general linear group. It also proves that block Levi matrices normalize the
block unipotent and block parabolic subgroups. Throughout, `ι` is a finite index type, `A` an
arbitrary commutative ring, `a : ι → ℤ` a weight vector, and `p : ι → Prop` a decidable
predicate. The predicate cuts out an index set `I = {i | p i}` with complement `I'`.

## The block lemma

`submatrix_mul_of_compl_zero` is a block multiplication rule. If `H` has no entries from rows
in `I'` to columns in `I`, then the columns `I` of `X * H` are the columns `I` of `X` times the
block `H_{II}`. The proof splits the sum over the middle index into `I` and `I'`.

`eq_zero_of_mul_of_compl_zero` is the block lemma for matrices. Assume:

* `V'` has the identity entry at every `(i, j)` with `a j ≤ a i`;
* `Q` vanishes at every `(i, j)` with `a i < a j`;
* `Q = V' * H`, where `H` has a left inverse `Hinv`;
* `H_{rs} = 0` whenever `r ∈ I'` and `s ∈ I`.

Then `Q_{rs} = 0` whenever `r ∈ I'` and `s ∈ I`.

The proof works with blocks. By the multiplication rule, `Q_{II} = V'_{II} H_{II}` and
`Q_{I'I} = V'_{I'I} H_{II}`. Its steps:

* `H_{II}` is invertible, since `Hinv_{II} H_{II}` is the identity block of `Hinv * H`.
* `V'_{II}` is block triangular for `a` with identity diagonal blocks, so its determinant is
  `1`.
* Hence `Q_{II}` is invertible.
* The matrix `E = Q_{I'I} Q_{II}⁻¹` has two expressions: `E = V'_{I'I} (V'_{II})⁻¹`, and
  `E = Q_{I'I} (Q_{II})⁻¹` by definition.
* Inverses of block triangular matrices are block triangular for the same weights.

Fix `r ∈ I'` and `s ∈ I`.

* If `a s ≤ a r`, use the first expression and look at a middle index `t ∈ I`. If
  `a t ≤ a r`, then `V'_{rt}` is an identity entry with `r ≠ t`, so it vanishes. Otherwise
  `a s < a t`, and the entry `(t, s)` of `(V'_{II})⁻¹` vanishes.
* If `a r < a s`, use the second expression. If `a t ≤ a r`, then `a t < a s`, and the entry
  `(t, s)` of `(Q_{II})⁻¹` vanishes. Otherwise `a r < a t`, and `Q_{rt}` vanishes.

So `E = 0`, and `Q_{I'I} = E Q_{II} = 0`.

`eq_zero_of_eq_mul_of_compl_zero` restates the lemma for invertible matrices. Let `H = V Q`,
with `V` in `blockUnipotentSubgroup A (-a)`, `Q` in `blockParabolicSubgroup A a`, and
`H_{rs} = 0` for `r ∈ I'` and `s ∈ I`. Then also `Q_{rs} = 0` for `r ∈ I'` and `s ∈ I`.
The proof applies the matrix lemma with `V' = V⁻¹`, which lies in the same block unipotent
subgroup, and `Hinv = H⁻¹`.

## Levi conjugation

* `blockLeviSubgroup_neg`: the block Levi subgroups of `a` and `-a` coincide.
* `blockLeviSubgroup_le_blockParabolicSubgroup`: the block Levi subgroup of `a` lies in the
  block parabolic subgroup of `a`.
* `blockUnipotentSubgroup_le_blockParabolicSubgroup`: so does the block unipotent subgroup
  of `a`.
* `conj_mem_blockUnipotentSubgroup`: for `L` block Levi and `V` block unipotent for `a`, the
  matrix `L⁻¹ V L` is block unipotent. It is block parabolic, and its block diagonal part is
  `L⁻¹ · 1 · L = 1` by multiplicativity of the block diagonal part on block parabolic matrices.
* `conj_mem_blockParabolicSubgroup`: for `L` block Levi and `Q` block parabolic, the matrix
  `L⁻¹ Q L` is block parabolic, because the block parabolic subgroup is a subgroup containing
  `L`.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd edition), prove Proposition 2.1.8(3) over
a field with a stabilizer argument (Step 3), using an embedding into `GL(V)` and the stabilizer
of a line. This development replaces the line by a coordinate subspace `k^I`. The present block
lemma is the matrix computation that this replacement needs. It is internal and is not taken
from the book.
