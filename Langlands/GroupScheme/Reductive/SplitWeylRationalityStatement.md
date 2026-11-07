# Rationality of the Weyl group of a split maximal torus: statement

Worker 835.

`Langlands.GroupScheme.SplitMaximalTorusWeylRationalityStatement.{u}` is a
proposition definition. This module does not prove it.

## The statement

Let `k` and `K` be fields in the universe `u`, with a `k`-algebra structure
on `K`, and write `b = algebraBaseMap k K : Spec K ⟶ Spec k`. Let `G` be a
group scheme over `Spec k` with `IsConnectedReductive G`. Let `T` be a
commutative group scheme over `Spec k` with `IsSplitTorus T.toGrp`, and let
`i : T.toGrp ⟶ G` be a maximal torus, `IsMaximalTorus i`.

Write `G_K = (GroupScheme.baseChange b).obj G`,
`T_K = (CommGroupScheme.baseChange b).obj T` and
`i_K = (GroupScheme.baseChange b).map i` for the actual base changes.
Suppose `n'` is a rational point of `G_K` and `σ' : T_K ≅ T_K` is an
automorphism with `IsNormalizingPoint i_K n' σ'`, that is,
`i_K ≫ (G_K.innerIso n').hom = groupHom σ'.hom ≫ i_K`. The statement asserts
that there are a rational point `n` of `G` and an automorphism `σ : T ≅ T`
with `IsNormalizingPoint i n σ` and
`(CommGroupScheme.baseChange b).mapIso σ = σ'`.

In words: every automorphism of `T_K` induced by conjugation by a `K`-point of
the normalizer of `T_K` is the base change of an automorphism of `T` induced
by conjugation by a `k`-point of the normalizer of `T`. Both normalizing
equations are equalities of group-scheme morphisms, so they hold on every test
scheme. The point `n` itself is not claimed to be related to `n'`; only the
induced torus automorphisms agree. This is the convention of the published
`IsNormalizingPoint.baseChangeBasePoint`, which pulls back a normalizing
point together with `(CommGroupScheme.baseChange b).mapIso` of its
automorphism.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (2017), source ID `milne-2017-algebraic-groups`,
Proposition 21.1, printed p.424 (PDF p.440):

> PROPOSITION 21.1. The Weyl group `W(G,T)` of a split reductive group `(G,T)`
> is a finite constant algebraic group. For every field `k'` containing `k`,
> `W(G,T)(k) = W(G,T)(k') = N(k')/T(k')`, `N = N_G(T)`.

Milne's proof notes that `Gal(k^s/k)` acts trivially on `X*(T)` because `T`
is split, so `W(G,T)` is constant. It then uses `H^1(k',T) = 1` for split `T`
(Milne 3.47), so `1 → T(k') → N(k') → (N/T)(k') → 1` is exact (Milne 3.45).

Here `(G,T)` split reductive means a connected reductive group with a split
maximal torus (Milne, beginning of §21.a, same page). This is the published
`IsConnectedReductive G`, `IsSplitTorus T.toGrp` and `IsMaximalTorus i`.
The registered 2017 errata snapshot
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for
Proposition 21.1 or printed p.424.

## Correspondence with the source

`W(G,T) = N_G(T)/T` acts faithfully on `T` (Milne, same page), so an element
of `W(G,T)(k')` is determined by the automorphism of `T_{k'}` it induces. The
proposition gives `W(G,T)(k) = N(k')/T(k')`, and `W(G,T)(k) = N(k)/T(k)` by
the same exact sequence over `k`. So every coset in `N(k')/T(k')` contains
the base change of a `k`-point of `N`, and the two induce the same
automorphism of `T_{k'}`. The Lean statement records exactly this
consequence: the automorphism `σ'` induced by an arbitrary normalizing
`K`-point is induced, after base change, by a normalizing `k`-point.

The statement does not identify `W(G,T)` with a constant group scheme or
represent `N_G(T)` by a scheme. It does not compare the points `n` and `n'`
modulo `T(K)`. Faithfulness and `C_G(T) = T` make the stated form equivalent
to the surjectivity of `N(k) → N(k')/T(k')`, but that equivalence is not
part of the statement.

## Intended use

For the root datum of a split maximal torus, a reflection of a root is first
realized over an algebraic closure, where the published rank-one results apply
(`RankOneCentralizerDetection.exists_nonidentityNormalizer`). This statement
then supplies a `k`-rational normalizing point inducing the same reflection.
