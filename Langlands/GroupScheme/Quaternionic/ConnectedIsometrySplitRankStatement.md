# Split rank of `O(q)⁰` equals the Witt index

Author: Worker 73.

Module `Langlands.GroupScheme.Quaternionic.ConnectedIsometrySplitRankStatement`, namespace
`Langlands.GroupScheme.Quaternionic`. It contains one `Prop`-valued definition,
`ConnectedIsometrySplitRankStatement`, with universe parameter `u`, and proves nothing. Its
proof is a separate task.

## The statement

```lean
def ConnectedIsometrySplitRankStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (degree : ℕ), Module.finrank K D = degree ^ 2 →
    ∀ (σ : FirstKindInvolution K D),
    Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom],
    σ.IsNondegenerateQuadratic q →
      splitRank (σ.connectedIsometryGroup q) = σ.quadraticWittIndex q
```

In words, take the following data:

* an arbitrary field `K`, with no restriction on the characteristic and no
  infiniteness or perfectness hypothesis;
* a finite-dimensional central division `K`-algebra `D` of degree `degree`, that is,
  `finrank K D = degree ^ 2`;
* an involution `σ` of `D` of the first kind (`FirstKindInvolution`, a `K`-linear
  anti-automorphism of order two) whose symmetric subspace `σ.symmetricSubspace` has
  `K`-dimension `degree * (degree + 1) / 2`;
* a finite coordinate type `n` and an element `q` of the published
  `σ.QuadraticForms n = M_n(D) ⧸ {x - ᵗx^σ}`, whose isometry group scheme `O(q)` is
  smooth.

If `q` is nondegenerate, so that its polar Gram matrix `Q + ᵗQ^σ` is invertible
(`IsNondegenerateQuadratic`), then the split rank of the identity component `O(q)⁰`
(`connectedIsometryGroup`) is the Witt index of `q`.

The objects are the published ones.

* `splitRank` (module `Rational.SplitTorus`) is the supremum, in `ℕ∞`, of the ranks of the
  split tori with a closed subgroup embedding into the group.
* `quadraticWittIndex` (module `Quaternionic.Forms`) is the largest `D`-dimension of a
  totally singular left `D`-subspace of `D^n`. On such a subspace the quotient-valued form
  `quadraticValue` vanishes identically.
* The natural-number Witt index is coerced to `ℕ∞`.

Smoothness of `O(q)` is a hypothesis because the Library defines `O(q)⁰` only for smooth
`O(q)`. This hypothesis matches the published `WittIndexOneSplitRankStatement`.

## The involution type and Tits's forms

The published quotient `M_n(D) ⧸ {x - ᵗx^σ}` uses a fixed sign. Tits 1968 instead uses a
sign `ε` equal to the type of the involution. For a type-`1` involution `ε = 1` and the two
quotients agree. For a type-`(-1)` (symplectic) involution in characteristic different
from 2 they differ: Tits's quotient divides by `x + ᵗx^σ`.

The hypothesis on the symmetric subspace restricts to the type-`1` case.

* In characteristic different from 2, `dim_K Sym(σ)` is `degree(degree+1)/2` for
  orthogonal (type `1`) involutions and `degree(degree−1)/2` for symplectic ones. The
  hypothesis therefore selects the orthogonal involutions, and the published quotient is
  Tits's quotient for `ε = 1`.
* In characteristic 2, `ε = −1 = 1`, so the fixed-sign quotient is Tits's for every
  involution of the first kind. Every involution of the first kind has symmetric
  subspace of dimension `degree(degree+1)/2`, so the hypothesis excludes nothing. This is
  the quadratic-pair case.

The hypothesis is the same as the one in the published
`AlignedSpinCoverTitsIndexStatement`, for which this statement is a prerequisite.

`IsNondegenerateQuadratic` (invertible polar matrix) is the nondefective case of Tits's
nondegeneracy. In characteristic 2, Tits 1968 §2.2 also admits nondegenerate forms of
defect one. Those forms are not covered here.

## Relation to published results

The published `WittIndexOneSplitRankStatement` (module `Quaternionic.IsometrySplitRank`)
treats Witt index one over an infinite field. It does not assume `D` central or a type
of involution. The present statement covers every Witt index and every field, finite
fields included, for central `D` and type-`1` involutions.

## Provenance

This statement is derived from the literature.

Borel–Tits 1965, 4.24 (source `borel-tits-1965-groupes-reductifs`, printed p. 99, PDF
p. 40) treats the ordinary case `D = K`, `σ = id`, `degree = 1`. It states that for a
nondegenerate quadratic form `Q` the `k`-rank of `O(Q)⁰` equals the index of `Q`, the
dimension of its maximal rational isotropic subspaces.

Tits 1966, Table II (source `tits-1966-classification-algebraic-semisimple`) covers the
division-algebra case. The Explanations (printed p. 54, PDF p. 59) state that `r` is the
relative rank. The type `D_n` entries (printed pp. 56–57, PDF pp. 61–62) describe the
groups of relative rank `r` in two ways. One uses `SO(D, h)`, where `h` is a hermitian
form of index `r` with respect to an involution whose symmetric space has dimension
`d(d+1)/2`, in characteristic different from 2. The other uses a nondegenerate,
nondefective generalized quadratic form of index `r`, in characteristic 2.

The `σ`-quadratic forms of type `1`, their polar forms and their Witt index are those of
Tits 1968 (source `tits-1968-formes-quadratiques-clifford`, §2.1, printed p. 20, PDF p. 3,
and §§2.2–2.3, printed pp. 21–23, PDF pp. 4–6). The published `Quaternionic.Forms` module
formalizes them with the fixed sign `ε = 1`. The present statement restates the rank
comparison with the Library's `splitRank`, `connectedIsometryGroup` and
`quadraticWittIndex`, for every field and every characteristic.
