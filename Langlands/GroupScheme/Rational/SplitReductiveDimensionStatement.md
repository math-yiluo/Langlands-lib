# The dimension of a split reductive group

`Langlands.GroupScheme.SplitReductiveDimensionStatement.{u}` is a Prop-valued
definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: let `k : Type u` be a field, let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`hG : IsConnectedReductive G`, let `T : CommGroupScheme (Spec (CommRingCat.of k))`
and let `t : T.toGrp ⟶ G` satisfy `IsSplitSubtorus t` and `IsMaximalTorus t`.
Then

```text
topologicalKrullDim G.X.left =
  topologicalKrullDim T.toGrp.X.left + ((relativeRoots t).ncard : WithBot ℕ∞)
```

In words: for a split reductive group `(G, T)` over `k`,
`dim G = dim T + |Φ(G, T)|`. (The `letI` in the Lean statement only supplies
the instance `IsAffineHom G.X.hom`, which is part of `IsConnectedReductive G`
and is needed to form the roots.)

The ingredients are existing declarations, used without change.

- `IsConnectedReductive G` (from [`Reductive.Basic`](../Reductive/Basic.md))
  says that `G` is smooth, affine and connected over `k`, and that the
  unipotent radical of its base change to an algebraic closure of `k` is
  trivial: `G` is a reductive group in Milne's sense (6.46).
- `IsSplitSubtorus t` (from [`SplitTorus`](SplitTorus.md)) says that `T` is a
  split torus and `t` is a closed subgroup (closed immersion).
  `IsMaximalTorus t` (from [`Torus.Maximal`](../Torus/Maximal.md)) says that
  `T` is a torus, `t` is a closed subgroup, and every factorization of `t`
  through a closed subgroup torus of `G` is by an isomorphism: `t` is a
  maximal torus of `G`. Together, `T` is a split maximal torus of `G`.
- `relativeRoots t` (from [`RelativeRoots`](RelativeRoots.md)) is the set
  `roots t` of [`Torus.Weights`](../Torus/Weights.md): the characters
  `χ ≠ 0` of `T` whose weight space `weightSpace t χ` in the Lie algebra of
  `G` is nonzero. The weight space consists of the `X ∈ Lie(G)` with
  `Ad(t(s)) X = χ(s) X` for all points `s` of `T` over all test algebras,
  where `Ad` is the adjoint representation on the Lie algebra
  `Ker(G(A[ε]) → G(A))`. So `relativeRoots t` is Milne's set `Φ(G, T)`.
  `Set.ncard` is its number of elements (the set is finite, since `Lie(G)`
  is finite-dimensional and weight spaces of distinct characters are
  independent).
- `topologicalKrullDim X` (Mathlib) is the supremum of the lengths of chains
  of irreducible closed subsets of the space `X`, with values in
  `WithBot ℕ∞`. It is applied to the underlying schemes `G.X.left` and
  `T.toGrp.X.left`.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Corollary 21.13, printed p. 430: "The dimension of G is
dim T + |Φ|." Its proof: "From g = t ⊕ ⨁_{α∈Φ} g_α and (b) of the theorem,
we see that dim g = dim t + |Φ|. This implies the statement because G and T
are smooth."

The context and definitions:

- Chapter 21 opening, printed p. 424: "The field k is arbitrary." Same page:
  "Let G be a reductive algebraic group over k." … "Recall also that G is
  split if some maximal torus T is split, in which case we refer to the pair
  (G, T) as a split reductive group."
- Roots, printed p. 425: "Let (G, T) be a split reductive group over k, and
  let Ad: G → GL_g be the adjoint representation (10.20). Then T acts on g
  and, because T is diagonalizable, g decomposes into a direct sum
  g = g_0 ⊕ ⨁_{α∈X(T)} g_α with g_0 = g^T and g_α the subspace on which T acts
  through a nontrivial character α. The characters α of T occurring in this
  decomposition are called the roots of (G, T). They form a finite subset
  Φ(G, T) of X(T)."
- In Corollary 21.13, `G` and `T` are those of Theorem 21.11 (printed
  p. 428: "Let (G, T) be a split reductive group over k").
- Dimension, A.47, printed p. 577: "Let X be an irreducible algebraic scheme
  over k. The dimension of X is the greatest length d of a chain of
  irreducible closed subschemes Z = Z_d ⊃ ⋯ ⊃ Z_1 ⊃ Z_0."

The provenance is derived for these reasons.

- Split reductive groups. Milne's reductive group is
  `IsConnectedReductive` (see [`Reductive.Basic`](../Reductive/Basic.md),
  which records the correspondence with Milne's 6.46). Milne's pair `(G, T)`,
  with `T` a split maximal torus, is given by the closed subgroup
  `t : T ⟶ G` with `IsSplitSubtorus t` and `IsMaximalTorus t`; the Lean
  statement quantifies over every such pair, so it applies to every split
  reductive group and every choice of split maximal torus.
- Roots. `relativeRoots t` is defined by the weight-space condition on the
  Lie algebra under the adjoint action of `T`, which is Milne's description
  of `Φ(G, T)`; see [`Torus.Weights`](../Torus/Weights.md), which records
  the same correspondence with §21.a. Milne's `|Φ|` is the number of roots,
  `(relativeRoots t).ncard`.
- Dimension. `G` and `T` are connected group varieties, hence irreducible,
  and Milne's dimension (A.47) is the supremum of lengths of chains of
  irreducible closed subsets of the underlying space, which is
  `topologicalKrullDim`. (Irreducible closed subschemes and irreducible
  closed subsets of the underlying space correspond through the reduced
  structure.) Both sides of the Lean equation are finite natural numbers
  for such `G` and `T`; the equation is stated in `WithBot ℕ∞`, the type of
  `topologicalKrullDim`.
- One universe `u` is used for `k` and the schemes. This is a formalization
  convention.

Relation to the Library. The Library has no statement of Corollary 21.13.
Related results:

- `weightDecompositionStatement` (in
  [`Reductive.WeightDecompositionProof`](../Reductive/WeightDecompositionProof.md))
  proves `WeightDecompositionStatement`: for a split torus `T` mapping to an
  affine `G` of finite type over `k`, the weight spaces form an internal
  direct sum decomposition of `Lie(G)`.
- `absoluteRootVectorLine` (in
  [`Absolute.RootVectorLineProof`](../Absolute/RootVectorLineProof.md))
  proves `AbsoluteRootVectorLineStatement`, the case of Theorem 21.11(c)
  over an algebraically closed field: every root group is a closed subgroup
  isomorphic to a one-dimensional vector group.
- `Lie.finrank_kernel_cast_eq_ringKrullDim` (in
  [`Lie.SmoothIsogenyDimension`](../Lie/SmoothIsogenyDimension.md))
  identifies the dimension of the Lie algebra of a smooth affine group with
  the Krull dimension of the local ring at the identity, and
  `Lie.finrank_kernel_cast_le_topologicalKrullDim` (in
  [`Lie.SubgroupCellDimension`](../Lie/SubgroupCellDimension.md)) bounds it by
  `topologicalKrullDim`.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Corollary 21.13 on
printed p. 429 with the same statement; its proof reads "As
g = t ⊕ ⨁_{α∈Φ} g_α, it follows from (b) of the theorem that
dim g = dim t + |Φ|. This implies the statement because G and T are
smooth." It has the definition of split reductive groups on printed p. 424,
the definition of roots on printed p. 425 with the same wording, Theorem
21.11 on printed p. 428, and A.47 on printed p. 581 with the same wording.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 424, 425, 428, 429, 430 or 577. The errata snapshot of
2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed pp. 424, 425, 428, 429 or 581.

## For the later proof (not part of this unit)

A proof of the Lean statement can follow Milne's argument.

- Lie algebra decomposition. By `weightDecompositionStatement`,
  `Lie(G) = ⨁_χ weightSpace t χ`. The weight space of `χ = 0` is the
  fixed subspace `Lie(G)^T`, which is `Lie(C_G(T))` (Milne 10.34) and equals
  `Lie(T)` because `C_G(T) = T` for a maximal torus of a reductive group
  (Milne 17.84). A proof must establish this identification for the
  Library's `weightSpace`.
- Root spaces are lines. For each root `α`, `weightSpace t α` is
  one-dimensional (Milne, Theorem 21.11(b)). Over an algebraically closed
  field this can be obtained from `absoluteRootVectorLine`; over a general
  `k`, the weight spaces must be compared with those of the base change to
  an algebraic closure, which do not change in dimension because `T` is
  split.
- Counting. Hence `dim_k Lie(G) = dim_k Lie(T) + |Φ(G, T)|`.
- From Lie algebras to dimensions. For a smooth connected affine group `H`
  over `k`, `dim_k Lie(H) = dim H`: the local ring at the identity is
  regular of dimension `dim_k Lie(H)`
  (`Lie.finrank_kernel_cast_eq_ringKrullDim`), and since `H` is irreducible,
  `dim H` is the Krull dimension of the local ring at every closed point
  (A.47), in particular at the identity. Apply this to `H = G` and to
  `H = T`.
