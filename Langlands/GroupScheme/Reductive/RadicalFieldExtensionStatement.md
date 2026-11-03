# Trivial unipotent radical under extension of algebraically closed fields

Author: Worker 1401.

`Langlands.GroupScheme.AlgebraicallyClosedRadicalFieldExtensionStatement.{u}`
is a proposition target. This module defines the proposition and supplies no
proof of it.

## The proposition

For all fields `k K : Type u` in one universe `u`, an instance
`Algebra k K`, instances `IsAlgClosed k` and `IsAlgClosed K`, and an actual
group scheme `G` over `Spec (CommRingCat.of k)`, the proposition asserts

```lean
Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
  HasTrivialUnipotentRadical G → HasTrivialUnipotentRadical G_K
```

where

```lean
G_K = (GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G
```

Here the displayed equality only fixes notation for this documentation.
`GroupScheme.baseChange f` is the published `(Over.pullback f).mapGrp`, so
`G_K` is the actual pullback group object over `Spec K` with its induced
group law. A ring map between fields is injective, so `Algebra k K` makes
`K` an arbitrary extension of `k`. Both fields are algebraically closed.
The extension may be transcendental, of any transcendence degree, for
example `K` an algebraic closure of `k(t)`. The characteristic is arbitrary.
There is no perfectness, cardinality or dimension condition. The trivial
group scheme satisfies all four hypotheses, so it is covered as well.

## Meaning of the predicates

All predicates are the published ones from
`Langlands.GroupScheme.Reductive.Basic`, used unchanged.

- `Smooth G.X.hom` and `IsAffineHom G.X.hom` say that the structure
  morphism `G → Spec k` is smooth and affine. Smoothness includes local
  finite presentation, and an affine morphism is quasi-compact, so `G` is a
  smooth affine group scheme of finite type over `k`. Over an algebraically
  closed field this is a linear algebraic group in Conrad's sense and an
  affine group variety in Milne's sense.
- `ConnectedSpace G.X.left` says that the underlying topological space of
  `G` is connected (and nonempty).
- `HasTrivialUnipotentRadical G` says: for every group scheme `H` over
  `Spec k` and every homomorphism `i : H ⟶ G` such that
  - `IsClosedSubgroup i` (the underlying scheme morphism is a closed
    immersion),
  - `Smooth H.X.hom`,
  - `ConnectedSpace H.X.left`,
  - `IsUnipotent H`, and
  - `(SubgroupFunctor.range i).IsNormal`,

  the subgroup functor `SubgroupFunctor.range i` equals `⊥`. The range
  assigns to every scheme `T` over the base the image of `H(T)` in `G(T)`;
  it is normal when this image is stable under conjugation by `G(T)` for
  every `T`; `⊥` is the identity subgroup on every `T`. So the predicate
  asks that every smooth connected unipotent normal closed subgroup be
  trivial, tested on all base schemes rather than on rational points.
- `IsUnipotent H` says that every matrix representation
  `ρ : MatrixRepresentation H n` with a nonempty finite index type
  `n : Type` has a nonzero fixed vector `v : n → k`. Fixedness is tested on
  every scheme over the base. This is Milne 6.45.

In the conclusion the same predicate is applied over `K`: `H` ranges over
all group schemes over `Spec K` with a closed-subgroup homomorphism to
`G_K`, including subgroups that do not descend to `k`, and unipotence is
tested by all representations over `K`. The conclusion is therefore not a
statement about rational points, and it cannot be obtained merely by base
changing subgroups of `G`.

The four hypotheses are exactly the four fields of `IsPseudoReductive G`.
Over an algebraically closed field they say that `G` is a connected
reductive group in the sense of Conrad's Definition 1.1.11 and Milne 6.46. The proposition deliberately does not assume
`IsConnectedReductive G`. That predicate tests the base change to the chosen
`AlgebraicClosure k`, a different type from `k` even when `k` is
algebraically closed, and assuming it would hide the comparison this
statement is meant to provide.

## Original sources and errata

- B. Conrad, *Reductive group schemes* (2014), registered source
  `conrad-2014-reductive-group-schemes`, SHA-256
  `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
  Printed page equals PDF page in the registered file.
  - The discussion after Definition 3.1.1, p.81: for any linear algebraic
    group `H` over an algebraically closed field `k` and any algebraically
    closed extension `K/k`, the inclusion `R_u(H)_K ⊂ R_u(H_K)` is an
    equality (see Exercise 3.4.1). The present proposition is the
    consequence that `R_u(G) = 1` implies `R_u(G_K) = 1` for connected `G`.
  - Exercise 3.4.1, p.104: for an extension `K/k` of algebraically closed
    fields and a connected reductive `k`-group `G`, the smooth connected
    affine `K`-group `G_K` is reductive. The indicated proof is by
    contradiction: (i) a non-reductive `G_K` contains a nontrivial normal
    `K`-subgroup `U` with a finite composition series with successive
    quotients `G_a`; (ii) writing `K` as the direct limit of its finitely
    generated `k`-subalgebras, `U` and the series spread out over some
    finitely generated `k`-subalgebra `A ⊂ K` as a smooth affine normal
    closed `A`-subgroup of `G_A` with a series `1 = U_0 ⊂ ⋯ ⊂ U_n = U`,
    `n > 0`, each `U_i` the kernel of an fppf homomorphism `U_{i+1} ↠ G_a`;
    (iii) specializing at a `k`-point of `Spec A` shows that `G` is not
    reductive.
  - Definition 1.1.11, p.11: a reductive `k`-group over an algebraically
    closed `k` is a linear algebraic group with `R_u(G) = 1`.
- J. S. Milne, *Algebraic Groups* (2017), registered source
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page `p` is PDF page `p + 16`.
  - Proposition 19.13, printed p.400 (PDF p.416): for an algebraic group
    variety `G` over `k` and a field `k'` containing `k`, `G` is reductive
    if and only if `G_{k'}` is reductive; its proof is "similar to that of
    Proposition 19.5". The present proposition is the forward direction when
    `k` and `k'` are both algebraically closed.
  - Proposition 19.5, printed pp.398–399 (PDF pp.414–415): the semisimple
    analogue. Its proof reduces to `k` and `k'` both algebraically closed and
    proves necessity by a spreading argument: a nontrivial smooth connected
    normal commutative subgroup of `G_{k'}` is defined over a finitely
    generated
    subfield, `G` and the subgroup extend to smooth group schemes over an
    open `Spm(A)`, and specialization at a maximal ideal with residue field
    `k` gives a nontrivial such subgroup of `G`.
  - 6.45 and 6.46, printed p.135 (PDF p.151): unipotent algebraic groups
    via nonzero fixed vectors; the unipotent radical `R_u(G)` of a connected
    group variety as the largest connected normal unipotent subgroup
    variety; over an algebraically closed field `G` is reductive when
    `R_u(G) = e`. Since `R_u(G)` contains every smooth connected normal
    unipotent subgroup, `R_u(G) = e` holds exactly when every such subgroup
    is trivial, which is what `HasTrivialUnipotentRadical` states without
    presupposing that the radical exists.
- Milne's official errata, registered source
  `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
  `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`, was
  read in full. Its Chapter 19 entries concern only Definitions 19.7 and
  19.8 (p.399); nothing corrects 6.45, 6.46, Proposition 19.5 or
  Proposition 19.13.

The sources work with functors on `k`-algebras and with subgroup varieties.
Here subgroups are closed-immersion homomorphisms and all scheme points are
tests, as everywhere in `Langlands.GroupScheme`; the correspondence of these
conventions is documented with `Langlands.GroupScheme.Reductive.Basic`.

## Scope

This is a statement target only. A proof must supply the substantive
argument indicated by the sources: finite-data spreading of a nontrivial
smooth connected normal unipotent subgroup of `G_K` (together with
whatever structure certifies unipotence and nontriviality, for example a
positive-length `G_a` series) over a finitely generated `k`-subalgebra of
`K`, and specialization at a `k`-point. None of this, nor any spreading-out
result, split-series criterion or radical-invariance bridge, is a premise
of the proposition. Only the preservation direction is stated; the reverse
reflection from `G_K` to `G` is not part of this target.

The intended consumer is the published field-extension target
`Langlands.GroupScheme.ConnectedReductiveFieldExtensionStatement`: after
choosing a `k`-embedding of `AlgebraicClosure k` into
`AlgebraicClosure K` and comparing iterated pullbacks, that target needs
exactly this preservation over the two chosen closures. Those comparisons
are not part of this module, and this module does not depend on that target.
