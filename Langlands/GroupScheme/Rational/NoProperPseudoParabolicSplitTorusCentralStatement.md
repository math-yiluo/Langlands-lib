# Split tori become central modulo the radical without proper pseudo-parabolics

Author: Worker 1413.

`Langlands.GroupScheme.NoProperPseudoParabolicSplitTorusCentralStatement.{u}`
is an unproved proposition at arbitrary universe `u`. For every field
`k : Type u` and actual group scheme `G` over `Spec (CommRingCat.of k)`, it
assumes that `G` is smooth, connected and affine
(`Smooth G.X.hom`, `ConnectedSpace G.X.left`, `IsAffineHom G.X.hom`) and that
`G` has no proper pseudo-parabolic subgroup, in the same form as the
published `NoProperPseudoParabolicSolvableEnvelopeStatement`:

```text
∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
  IsPseudoParabolicSubgroup i → IsIso i.
```

It further takes

- an actual group scheme `U` and a homomorphism `r : U ⟶ G` with
  `IsUnipotentRadical r` (a represented ground-field unipotent radical
  `R_{u,k}(G)`);
- an actual group scheme `Q` and a homomorphism `q : G ⟶ Q` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q` and
  `IsPseudoReductive Q`;
- a commutative group scheme `S` and a homomorphism `i : S.toGrp ⟶ G` with
  `IsSplitSubtorus i`.

It concludes `IsCentral (i ≫ q)`: every point of `S`, on every relative
scheme test `T` over `Spec k`, maps into the centre of `Q` on that test.

## Published interfaces

The module imports `Langlands.GroupScheme.PseudoParabolic`,
`Langlands.GroupScheme.Rational.SplitTorus` and
`Langlands.GroupScheme.Rational.Characters` unchanged. All predicates are
used as published:

- `IsPseudoParabolicSubgroup i` is the represented fppf-local product
  `P_G(χ) R_{u,k}(G)` for some actual ground-field cocharacter `χ`.
- `IsUnipotentRadical r` says that `r` is a closed subgroup with smooth,
  connected, unipotent source and normal image, greatest among such normal
  subgroups over `k`.
- `RelativeRoot.IsFppfQuotient N q` says that the underlying scheme map of
  `q` is flat, surjective and locally of finite presentation and that the
  all-test image of its actual kernel is `N`.
- `IsPseudoReductive Q` consists of smoothness, affineness, connectedness and
  triviality of the ground-field unipotent radical of `Q`.
- `IsSplitSubtorus i` says that `S.toGrp` is a split torus and `i` is a
  closed subgroup.
- `IsCentral f` for `f : H ⟶ Q` says that `x ≫ f.hom.hom` lies in
  `(center Q).carrier T` for every test `T` and every point `x : T ⟶ H.X`.

The pseudo-reductivity of `Q` is a hypothesis rather than a conclusion: it is
supplied by the published `UnipotentRadicalQuotientStatement` for the same
`r`. The statement does not require that a radical or a quotient exist; it
only speaks about supplied ones.

## Source and derived provenance

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Printed page `p` is PDF page `p + 26`.

- Definition 2.2.1, printed p.62 (PDF p.88): pseudo-parabolic subgroups
  `P_G(λ) R_{u,k}(G)`.
- Lemma 2.2.3, printed pp.62–63 (PDF pp.88–89): (1) `G` has a proper
  pseudo-parabolic `k`-subgroup if and only if `G/R_{u,k}(G)` contains a
  non-central `k`-split `k`-torus; (2) for pseudo-reductive `G`, `P_G(λ)` is
  proper if and only if `λ(GL_1)` is not central.
- The proof of Theorem C.2.3, printed pp.593–594 (PDF pp.619–620), uses
  Lemma 2.2.3 in the form "if `G` has no proper pseudo-parabolic subgroup,
  all `k`-split tori of `G` map into the maximal central `k`-split torus of
  `G/U`".

This statement is derived. It records the consequence of the "if" direction
of Lemma 2.2.3(1) used in Theorem C.2.3: the image in `G/R_{u,k}(G)` of a
split subtorus of `G` is a `k`-split torus, so in the absence of proper
pseudo-parabolic subgroups it is central. It is formulated for the composite
homomorphism `i ≫ q` rather than for an image subgroup, so no image of `S` in
`Q` has to be constructed. The quotient `G/R_{u,k}(G)` is represented by the
supplied fppf quotient `q`, as in `UnipotentRadicalQuotientStatement`. No
project errata file for this source was present when this statement was
prepared.

## Retained proof obligations

This file defines a proposition and supplies no proof. A proof must, for
each cocharacter `λ` of `S`, relate the published pseudo-parabolic predicate
to the dynamic parabolic subgroups of `G` and `Q`: it must represent
`P_G(λ) R_{u,k}(G)` as an actual closed subgroup satisfying
`IsPseudoParabolicSubgroup`, deduce from the hypothesis that it is all of `G`,
show that `q` maps `P_G(λ)` into `P_Q(q ∘ λ)`, and then use
pseudo-reductivity of `Q` (Lemma 2.2.3(2)) to show that `q ∘ λ` is central.
Finally it must pass from centrality of all cocharacters of the split torus
`S` to `IsCentral (i ≫ q)` on every relative scheme test.
