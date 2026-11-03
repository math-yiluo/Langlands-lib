# Descent of group-like spanning over a separably closed field

This file accompanies
`Langlands.CoalgebraDescent.SeparablyClosedGroupLikeSpanningStatement.{u,v,w}`.
It defines a proposition; it does not prove that proposition.

## Exact statement and conventions

The universes `u`, `v`, and `w` are arbitrary and independent. The proposition
universally quantifies, in this order, over:

- `k : Type u`, with instances `[Field k]` and `[IsSepClosed k]`;
- `C : Type v`, with instances `[AddCommGroup C]`, `[Module k C]`, and
  `[Coalgebra k C]`;
- `K : Type w`, with instances `[Field K]` and `[Algebra k K]`.

For each such choice, the asserted implication is exactly

```lean
Submodule.span K {x : K ⊗[k] C | IsGroupLikeElem K x} = ⊤ →
  Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤
```

The tensor product carries Mathlib's scalar-extension coalgebra, obtained from
`TensorProduct.instCoalgebra` in `Mathlib.RingTheory.Coalgebra.TensorProduct`
with the left coalgebra equal to `K` over itself. There is no separate coalgebra
structure parameter on the tensor product. The predicate is Mathlib's
`IsGroupLikeElem`: an element `x` satisfies `counit x = 1` and
`comul x = x ⊗ x`, with both coalgebra maps and the latter tensor product taken
over the field named in the predicate. Each span is the linear span over its
displayed field, and `⊤` is the entire corresponding vector space.

There is no finite-dimensionality assumption on `C`, no cocommutativity or
multiplication assumption on `C`, no perfectness or characteristic assumption on
`k`, and no finiteness, algebraicity, or separability assumption on `K/k`.
No Hopf algebra, algebraic group, torus, splitting data, or descent certificate
is quantified. The zero-dimensional coalgebra is included: its group-like set
is empty, and its span and top submodule coincide.

## Source correspondence

The primary source is James S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (2017), Chapter 12, printed pp.236–238,
PDF pages 252–254 (one-based), especially the definition of coetale coalgebras
on p.237 and Theorem 12.18(c) ⇒ (d) on p.238.
The registered source ID is `milne-2017-algebraic-groups`, with SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The retained PDF is
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.

Milne's printed theorem concerns algebraic groups. In the indicated implication,
a finite-dimensional subcoalgebra of the coordinate coalgebra has a commutative
etale dual. Over a separably closed field this dual is a finite product of copies
of the field, and its coordinate functionals give a group-like basis of the
subcoalgebra. The union of finite-dimensional coefficient subcoalgebras then
gives spanning of the entire coordinate coalgebra. The Lean proposition extracts
the coalgebra argument and adds descent from the arbitrary extension `K/k`.
It is a derived statement, not a verbatim statement of Theorem 12.18.

The complete official errata snapshot, registered as
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was checked. Its Chapter 12 corrections concern 12.41 and 12.57; neither changes
the passage used here.

## Derivation rationale and remaining proof obligations

The following is the proposed mathematical derivation, not an implemented Lean
proof and not a list of extra hypotheses.

1. Every element of a coalgebra over a field lies in a finite-dimensional
   subcoalgebra `D`. Scalar extension embeds `K ⊗[k] D` as a subcoalgebra of
   `K ⊗[k] C`, since a field extension is faithfully flat.
2. The assumed spanning and linear independence of distinct group-like elements
   give a diagonal basis of `K ⊗[k] C`. A subcoalgebra of a coalgebra with a
   group-like basis is a coordinate subspace: applying a coordinate functional
   to one factor of the comultiplication isolates each nonzero coordinate
   multiple of a basis element and places that element in the subcoalgebra.
   A finite-dimensional subcoalgebra therefore has a finite group-like basis.
3. The convolution dual of `K ⊗[k] D` is consequently a finite product of copies
   of `K`. Finite-dimensional dual base change identifies it with the scalar
   extension of the convolution dual of `D`. Thus commutativity and etaleness
   of the latter dual follow by faithfully flat descent. These are the
   additional descent steps needed before applying Milne's coetale argument.
4. A finite commutative etale algebra over the separably closed field `k` is a
   finite product of copies of `k`. Dualizing its coordinate projections gives
   a group-like basis of `D`, as in Milne 12.18(c) ⇒ (d). The empty product
   covers `D = 0`.
5. The finite-dimensional subcoalgebras cover `C`, so their group-like bases
   imply the required spanning over `k`.

None of these five steps is claimed as a proved declaration in this module.
A proof should reuse Mathlib's `linearIndepOn_isGroupLikeElem` and the existing
convolution algebra `WithConv (D →ₗ[k] k)` from
`Mathlib.RingTheory.Coalgebra.Convolution`. The required subcoalgebra
constructions, local finite-dimensionality, coordinate closure, dual base change,
and etale descent must be supplied by proofs; they are not premises of this
statement. No antipode or group operation is used in this derivation.
