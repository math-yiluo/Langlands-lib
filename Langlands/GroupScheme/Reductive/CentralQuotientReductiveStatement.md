# Statement: quotients of connected reductive groups by central subgroups

Authors: Worker 1428 (draft) and Worker 1499 (source check and Markdown
revision).

This module states one unproved proposition, the `Prop`-valued `def`
`Langlands.GroupScheme.CentralQuotientReductiveStatement` with one universe
parameter `u`. Nothing is proved here, no quotient is constructed, and no
other declaration is introduced.

The module imports `Langlands.GroupScheme.Reductive.Basic`,
`Langlands.GroupScheme.Rational.Characters` and
`Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`. It reuses by
name the Library declarations `GroupScheme`, `SubgroupFunctor` (with its
order `≤`), `center`, `IsConnectedReductive` and
`RelativeRoot.IsFppfQuotient`.

## The statement

```lean
def CentralQuotientReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
    (N : SubgroupFunctor G),
    IsConnectedReductive G → IsAffineHom Q.X.hom → LocallyOfFiniteType Q.X.hom →
    N ≤ center G → RelativeRoot.IsFppfQuotient N q →
      IsConnectedReductive Q
```

In words: let `k : Type u` be an arbitrary field (no perfectness,
separable-closedness or characteristic hypothesis), `G` and `Q` group schemes
over `Spec k`, `q : G ⟶ Q` a homomorphism and `N` a subgroup functor of `G`.
Assume

1. `IsConnectedReductive G` (`Reductive/Basic.lean`): `G` is smooth, affine
   and connected over `Spec k`, and its base change to `AlgebraicClosure k`
   has trivial unipotent radical in the sense of `HasTrivialUnipotentRadical`:
   for every closed subgroup `i : H ⟶ G_K` (with `K = AlgebraicClosure k`)
   such that `H` is smooth, connected and unipotent and the range of `i` is
   normal, the range of `i` is trivial;
2. `Q.X.hom` is affine and locally of finite type;
3. `N ≤ center G`: on every test scheme `T` over `Spec k`, every `T`-point
   of `N` lies in the scheme-theoretic centre `center G` of
   `Rational/Characters.lean`, that is, for every `a : T' ⟶ T` its
   restriction along `a` commutes with every `T'`-point of `G`;
4. `RelativeRoot.IsFppfQuotient N q`
   (`Rational/RootSubgroupStructureStatement.lean`): the underlying scheme
   morphism of `q` is flat, surjective and locally of finite presentation,
   and the range of the actual scheme kernel of `q` is `N` on every test
   scheme.

Then `IsConnectedReductive Q`.

No smoothness, reducedness, finiteness or multiplicative-type hypothesis is
placed on `N`; it may be nonsmooth (for example `μ_p` in `SL_p` in
characteristic `p`) or positive-dimensional (for example the central torus of
`GL_n`). The existence of such a `q` is not asserted here; for a normal
closed subgroup of a smooth affine group it is the published statement
`NormalSubgroupQuotientStatement`, proved in the Library by
`normalSubgroupQuotient`.

### Relation to the full-centre case

Taking `N := center G` (with `le_rfl` for the hypothesis `N ≤ center G`)
turns this statement into the published `CenterQuotientReductiveStatement`
(`Adjoint/CenterQuotientStatement.lean`), which has the same remaining
hypotheses and conclusion. That full-centre case is proved in the Library by
`centerQuotientReductive` (`Adjoint/CenterQuotientReductiveProof.lean`). The
present statement generalizes it to an arbitrary central kernel `N`.

## Why it is true (derived statement)

The statement is derived, not quoted. Source: J. S. Milne, *Algebraic Groups*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`;
printed page = PDF page − 16. Milne states the full-centre case: Corollary
17.62(e) (printed p.372, PDF p.388; proof on printed p.373, PDF p.389) says
that `G/Z(G)` has trivial centre for a reductive group `G`, and Remark 17.63
(printed p.373, PDF p.389) says that this quotient is an adjoint group, that
is, semisimple with trivial centre, hence reductive (6.44 and 6.46, printed
p.135, PDF p.151). Lemma 19.14 (printed p.400, PDF p.416) gives the converse
direction for isogenies: if `G' → G` is an isogeny of connected group
varieties and `G` is reductive, so is `G'`. Milne does not state the present
statement for an arbitrary central kernel. The following argument uses only
results stated in Milne.

Reductive means: a connected group variety whose geometric unipotent radical
is trivial (6.46, printed p.135, PDF p.151). Smoothness and connectedness of
`Q` follow from those of `G` because `q` is faithfully flat (the Library
proves `RelativeRoot.IsFppfQuotient.smooth_target` and
`RelativeRoot.IsFppfQuotient.connectedSpace`); affineness of `Q` is assumed.
For the unipotent radical, base change to `K = AlgebraicClosure k` preserves
the hypotheses, so suppose that `k = K` is algebraically closed, and let
`U ⊆ Q` be a smooth connected unipotent normal closed subgroup.

1. Let `H = q⁻¹(U)`, a normal closed subgroup of `G`, and let `M` be the
   identity component of its reduced subgroup. Then `M` is smooth, connected
   and normal in `G`. Since `q` is surjective on `K`-points, `q(M)` is a
   closed subgroup of finite index in the connected group `U`, so
   `q(M) = U`.
2. The kernel of `M → U` is `M ∩ N`, which lies in the centre of `G`, hence
   in the centre of `M`. Every unipotent algebraic group is nilpotent (Milne
   Proposition 14.21, printed p.284, PDF p.300), so `M`, a central extension
   of `U`, is nilpotent.
3. The connected nilpotent group varieties over a perfect field are exactly
   the products `U' × T` of a connected unipotent group variety `U'` and a
   torus `T` (Milne Corollary 16.48, printed p.341, PDF p.357). So
   `M = M_u × M_t`. Every unipotent subgroup of `M` maps trivially to `M_t`
   (Milne Corollary 14.18(a), printed p.284, PDF p.300), so `M_u` is the
   largest unipotent subgroup of `M`; hence conjugation by every element of
   `G(K)` preserves `M_u`, and `M_u` is a smooth connected unipotent normal
   subgroup of `G`. As `G` is reductive, `M_u = e` and `M = M_t` is a torus.
4. The restriction `M → U` of `q` is a homomorphism from a torus to a
   unipotent group, hence trivial (Milne Corollary 14.18(b), printed p.284,
   PDF p.300: there are no nontrivial homomorphisms from a group of
   multiplicative type to a unipotent group). As it is surjective, `U = e`.

Hence the geometric unipotent radical of `Q` is trivial. This argument is a
suggestion for a proof, not part of the statement.

The official Milne errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for 6.44,
6.46, 14.18, 14.21, 16.48, 17.62, 17.63 or 19.14.

## Use

This statement is intended to supply the reductivity of the quotient in the
proof of `SplitCentralTorusQuotientStatement` (planned module
`Reductive/CentralTorusQuotientStatement`, statement task
`2ea05a8b-453e-49c8-8d20-9b2ad61ac047`, not yet published when this module
was written), where `N` is the image in `G` of the finite kernel of an
isogeny of split tori.
