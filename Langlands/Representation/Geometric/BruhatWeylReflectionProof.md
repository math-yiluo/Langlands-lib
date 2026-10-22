# Weyl-class reflection from a determinant term

Author: Worker 179.

`Langlands.Geometric.padicBruhatWeylReflection` proves exactly the published
`Langlands.Geometric.PadicBruhatWeylReflectionTheorem.{u}` from
`Langlands.Representation.Geometric.BruhatMatrixStatement`. The statement and
its dependencies are imported without modification. Every prime, every actual
p-adic field in the arbitrary carrier universe, every positive rank, every
ordered positive pair of block shapes, and all actual permutations remain
quantified. The conclusion is equality of Weyl double-coset classes; neither
permutation is assumed minimal.

The proof first establishes the stronger theorem
`Langlands.Geometric.weyl_doubleCoset_eq_of_inverse_permutation_eq` over any
nontrivial commutative ring and any natural rank, including zero. The p-adic
proof is its direct specialization. The stronger result concerns the same
actual invertible matrices, block parabolics, block-preserving permutations,
and double-coset quotients as the target.

## Implemented proof

Write `P_v` and `P_w` for the published permutation matrices, which send `e_j`
to `e_(v j)` and `e_(w j)`. Equality of their inverse matrix classes gives
`a ∈ P_B` and `b ∈ P_C` with

```text
P_v⁻¹ = a P_w⁻¹ b,
a = P_v⁻¹ b⁻¹ P_w.
```

Since `a` is an invertible matrix over a nontrivial commutative ring, its
determinant is nonzero. Expanding the determinant proves that there is a
permutation `σ` for which every entry `a_(σ j,j)` is nonzero. This step is
proved by contradiction: if each permutation term had a zero selected entry,
every product in the determinant sum would vanish. It requires no assumption
that the coefficient ring is a domain.

An entry of an upper block parabolic matrix can be nonzero only when its row
block index is at most its column block index. Applying this to `a` gives

```text
blockIndex B (σ j) ≤ blockIndex B j.
```

The displayed identity for `a` and the published permutation-matrix entry
lemmas identify `a_(σ j,j)` with `(b⁻¹)_(v(σ j),w j)`. Since `b⁻¹ ∈ P_C`,
this also gives

```text
blockIndex C (v (σ j)) ≤ blockIndex C (w j).
```

For each inequality, the sums of the natural-valued block indices agree:
reindexing a finite sum by a permutation leaves it unchanged. The lemma
`Finset.sum_eq_sum_iff_of_le` therefore makes each pointwise inequality an
equality. It follows that `σ ∈ W_B` and `v σ w⁻¹ ∈ W_C`. Finally,

```text
v = (v σ w⁻¹) w σ⁻¹
```

supplies the Weyl double-coset witnesses, with left subgroup `W_C` and right
subgroup `W_B`, as required by the inverse matrix convention.

## Provenance and scope

This is an internal algebraic proof of the existing target. The target's
published Markdown records its derivation from the quotient bijection in
Bernstein–Zelevinsky (1977), section 6.4; this proof does not claim to reproduce
that source's argument. Its implemented determinant argument uses the existing
Library matrix entry and parabolic membership lemmas and Mathlib's determinant
expansion and finite-sum identities. No Bruhat decomposition, rank or orbit
classification, injectivity assertion, or representative uniqueness assertion
is assumed. All three supporting lemmas are private and proved in this file.
