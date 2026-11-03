# Unipotence of the upper unitriangular group scheme over a field

`Langlands.GroupScheme.UnitriangularUnipotentStatement.{u}` is a
Prop-valued statement at arbitrary universe `u`. For every field
`k : Type u` and every natural number `N`, it asserts

```lean
IsUnipotent (GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k)
  (fun i => -(i.val : ℤ)))
```

There is no restriction on the characteristic or algebraic closedness of
`k`, and no positivity assumption on `N`. This module defines the
proposition; it supplies no proof of it.

## Concrete scheme and its points

The scheme is the existing
`GeneralLinear.blockUnipotentScheme` from
`Langlands.GroupScheme.CorepresentedClosedSubgroup`. For weights
`e : Fin N → ℤ`, its coordinate ring is the quotient of the coordinate
ring of `GL_N` by the functions `x_ij - δ_ij` at positions with
`e i ≤ e j`. Its inclusion is `GeneralLinear.blockUnipotentHom`.

The existing theorem `GeneralLinear.isRepresentedBy_blockUnipotent`
identifies the image of this inclusion on every test scheme
`T` over `Spec k` with the subgroup functor
`GeneralLinear.blockUnipotent`. Under `GeneralLinear.pointsEquiv`, the
existing formula `GeneralLinear.mem_blockUnipotent` says that its
matrices `M` over `Γ(T, 𝒪_T)` satisfy

```text
e i ≤ e j  implies  M_ij = δ_ij.
```

For the specified weights `e i = -(i.val : ℤ)`, the weight inequality is
equivalent to `j.val ≤ i.val`. Thus the diagonal entries are `1`, the
entries strictly below the diagonal are `0`, and there are no equations
on the entries strictly above the diagonal. These are precisely upper
unitriangular matrices. Such matrices are invertible over every
commutative ring: for `N > 0`, write `M = I + A`, where `A` is strictly
upper triangular, and use `A^N = 0` and the finite geometric series for
the inverse. This description therefore imposes no additional condition
on the upper entries.

These point comparisons apply to all test schemes, including nonaffine
and nonreduced schemes; they do not rely on the density of field-valued
points. They explain the correspondence of the existing concrete scheme
with the usual `U_N`. No new comparison theorem is proved in this module.
For `N = 0`, the unique empty matrix gives the trivial group functor.
The statement includes this case, whose mathematical interpretation is
that the trivial group scheme is unipotent.

## Meaning of unipotence

`IsUnipotent` is the existing predicate from
`Langlands.GroupScheme.Reductive.Basic`. It quantifies over every
index type `n : Type` with `Fintype`, `DecidableEq`, and `Nonempty`
instances, and every
`ρ : MatrixRepresentation U_N n`. It requires a vector
`v : n → k` with `v ≠ 0` and `ρ.IsFixedVector v`.
The fixed-vector condition tests every scheme over `Spec k` and every
point of `U_N` on that scheme, after applying the structure ring map to
the coordinates of `v`.

Thus the conclusion concerns every nonzero finite-dimensional coordinate
representation of the group scheme. Choosing a finite basis gives this
coordinate formulation from the usual representation formulation.

## Literature correspondence

The registered original is J. S. Milne, *Algebraic Groups: The Theory of
Group Schemes of Finite Type over a Field* (2017), source
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

Section 14.b, printed p. 280 (PDF p. 296), recalls the fixed-vector
definition of unipotence and explains why finite-dimensional
representations suffice. Theorem 14.5, printed pp. 281–282
(PDF pp. 297–298), states the equivalence between unipotence and being
isomorphic to an algebraic subgroup of some `U_n`. Apply
direction (b)⇒(a) to `U_N` itself, with its identity inclusion.
Corollary 14.6, printed p. 282 (PDF p. 298), gives the equivalent
faithful-unipotent-representation formulation.

Milne works with algebraic groups, hence group schemes of finite type
over a field. The upper unitriangular scheme has freely chosen upper
entries, so it is represented by a polynomial algebra in the finitely
many variables `x_ij` with `i < j`; it is in that setting. For `N = 0`
the trivial group is covered by its identity embedding into `U_1`,
without requiring a zero-dimensional convention for Milne's notation.
The all-test matrix description and this zero-dimensional interpretation
are the implementation correspondence explained above, rather than
additional results attributed to the printed theorem.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read. It gives no
correction to Theorem 14.5 or Corollary 14.6.

The statement provides the focused target for the separate unitriangular
unipotence proof task `12a27202-6649-431d-9786-2c6600bc08ad`.
