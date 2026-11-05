# Minimal-norm weights in a coset of the root lattice

Let `P : RootDatum J X Y` have a finite index type, and let `B = P.RootForm` be its
canonical symmetric form, `B(x, y) = Σ_i ⟨x, α_i^∨⟩⟨y, α_i^∨⟩`. This form takes
nonnegative integer values on the diagonal. For `w ∈ X`, this module studies the
elements of minimal norm `B(ν, ν)` in the coset `w + ℤΦ`, where `ℤΦ = P.rootSpan ℤ`.
They form a finite set of weights. The set is stable under every reflection, and each
of its elements pairs with every coroot to `−1`, `0` or `1`.

The Chevalley construction uses these sets as the weights of small integral
representations: on the span of such a set, each root acts with strings of length at
most two. Together with the adjoint representation, these representations have weights
that generate `X`. If `w` is orthogonal to all coroots, then `B(w + q, w + q) = B(q, q)`
for `q ∈ ℤΦ`. So the set is `{w}`, which gives the one-dimensional summands for the
characters of `X` that are trivial on the coroots.

## Definitions

- `minNorm P w : ℕ` is the least value of `B(ν, ν)` for `ν ∈ w + ℤΦ`, defined with
  `Nat.find`.
- `minimalWeights P w : Set X` is the set of `ν` with `ν − w ∈ ℤΦ` and
  `B(ν, ν) = minNorm P w`.

## Results

- `rootForm_sub_root`, `rootForm_add_root`:
  `B(x ∓ α_j, x ∓ α_j) = B(x, x) − (±⟨x, α_j^∨⟩ − 1) B(α_j, α_j)`. These follow from
  `two_mul_rootForm_root` in `IntegralBase`.
- `exists_minNorm`, `minNorm_le`: the minimum is attained, and it is a lower bound on
  the coset.
- `minimalWeights_nonempty`: the set is nonempty.
- `pairing_le_one`, `neg_one_le_pairing`: for `ν` in the set and every `j`,
  `−1 ≤ ⟨ν, α_j^∨⟩ ≤ 1`. If `⟨ν, α_j^∨⟩ ≥ 2`, then `ν − α_j` lies in the same coset and
  has norm at most `B(ν, ν) − B(α_j, α_j) < B(ν, ν)`, because `B(α_j, α_j) ≥ 4`. The
  other bound is symmetric.
- `reflection_mem_minimalWeights`: `s_j ν = ν − ⟨ν, α_j^∨⟩ α_j` stays in the coset. It
  has the same norm because `B` is invariant under reflections (Mathlib's
  `rootForm_reflection_reflection_apply`).
- `eq_of_pairing_eq`: two elements of the set that pair equally with every coroot are
  equal. Their difference lies in `ℤΦ`, and a nonzero element of `ℤΦ` pairs nontrivially
  with some coroot.
- `minimalWeights_finite`: the set is finite. By the last two items, the map
  `ν ↦ (⟨ν, α_j^∨⟩)_j` is injective on it with values in `{−1, 0, 1}^J`.
- `root_mem_rootSpan`: each root lies in `ℤΦ`.

## Provenance

Classically one uses minuscule weights instead: each coset of the root lattice in the
weight lattice of a semisimple root system contains a minuscule weight (the theory of
minuscule weights in Bourbaki, *Lie groups and Lie algebras*, Chapters VI and VIII).
This module neither states nor uses that fact. Working with the norm minimum
instead is internal to this project. It needs no base, no dominance and no
semisimplicity, and it applies directly to a root datum with a radical. The argument is
the elementary norm-decrease computation above.
