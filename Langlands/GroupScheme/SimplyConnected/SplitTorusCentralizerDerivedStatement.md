# Derived subgroups of split-torus centralizers in simply connected groups

Authors: Worker 1532 and Worker 1413.

`Langlands.GroupScheme.SplitTorusCentralizerDerivedSimplyConnectedStatement.{u}`
is a proposition definition, not a proof. It states that for the
centralizer `M = Z_G(A)` of a split subtorus `A` of a simply connected
group `G`, the derived subgroup `M_der` is simply connected.

## The proposition

For every field `k : Type u`, every
`G : GroupScheme (Spec (CommRingCat.of k))` with `IsSimplyConnected G`,
every `A : CommGroupScheme (Spec (CommRingCat.of k))` and
`a : A.toGrp ⟶ G` with `IsSplitSubtorus a`, every
`M : GroupScheme (Spec (CommRingCat.of k))` and `j : M ⟶ G` with
`(torusCentralizer a).IsRepresentedBy j`, and every
`D : GroupScheme (Spec (CommRingCat.of k))` and `d : D ⟶ M` with
`IsDerivedSubgroup d`, the conclusion is `IsSimplyConnected D`.

These are all the quantified data and hypotheses. The universe `u` is
arbitrary. The field `k` has no perfectness, separability or
characteristic hypothesis, and `G` is not assumed quasi-split.

## Exact objects

- `IsSimplyConnected` (module `Langlands.GroupScheme.SimplyConnected.Basic`)
  says that the group is semisimple (`IsSemisimple`: connected reductive
  with finite scheme-theoretic centre) and that every central isogeny onto
  it from a semisimple group is an isomorphism. The conclusion
  `IsSimplyConnected D` therefore also says that `D` is semisimple.
- `IsSplitSubtorus a` (module `Langlands.GroupScheme.Rational.SplitTorus`)
  says that `A` is a split torus, that is, isomorphic to `splitTorus` on a
  finite index type, and that `a` is a closed immersion
  (`IsClosedSubgroup a`).
- `(torusCentralizer a).IsRepresentedBy j` (modules
  `Langlands.GroupScheme.Rational.TorusCentralizer` and
  `Langlands.GroupScheme.SubgroupFunctor`) says that `j` is a monomorphism
  of schemes over `Spec k` whose range on every test scheme is the
  centralizer functor of `a`: the points of `G` that commute with every
  point of `A` after every refinement of the test scheme. So `M` is
  `Z_G(A)`. Closedness of `j` is not part of this predicate.
- `IsDerivedSubgroup d` (module `Langlands.GroupScheme.Derived.Basic`) says
  that `d` is a closed immersion whose range is `derivedSubgroup M`, the
  intersection of the ranges of all closed subgroups of `M` that contain
  every commutator on every test scheme. So `D` is the scheme-theoretic
  derived subgroup of `M`.

## Source and derived formulation

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page = PDF page − 31.

- The proof of Lemma 2.6.27, printed p. 105 / PDF p. 136, takes a minimal
  Levi subgroup `M_0` of a simply connected `G` and says that the derived
  subgroup of `M_0` "is simply connected". The proof ends with
  `t⁻¹ m ∈ M_0,der(K) ⊂ M_0(K)^0`. KP give no separate reason for the
  last inclusion. One reading: `(M_0)_K` is quasi-split, so
  Definition 2.6.23(1) gives `M_0(K)^0 ⊇ M_0(K)^♮`. By Definition 2.6.20,
  `M_0(K)^♮` is the image of `M_0,sc(K)`, and this image is `M_0,der(K)`
  once `M_0,der` is simply connected.
- §2.6(a), printed p. 93 / PDF p. 124, fixes the notation `G_der` for the
  derived subgroup and `G_sc` for the simply connected cover of `G_der`.

The authors' list of corrections and additions (version of 1 November
2024, registered as `kaletha-prasad-2024-corrections`) has no entry for
Lemma 2.6.27.

The proposition is a derived formulation and not a numbered result of KP.
It replaces "minimal Levi subgroup" by "centralizer of a split subtorus".
In KP's use, `M_0 = Z_G(S)` for a maximal split `k`-torus `S`, and over `K`
one has `(M_0)_K = Z_{G_K}(S_K)` with `S_K` split, although `(M_0)_K`
need not be a minimal Levi subgroup of `G_K`. This centralizer form
matches the Library datum `ZeroSubgroupDatum`
(`Langlands.Geometry.Building.KPZeroSubgroups`), whose field
`isRepresentedBy` supplies `M_0` through
`(torusCentralizer i).IsRepresentedBy j` for a maximal split torus `i`.

The following standard argument is the provenance of the proposition. It
is not proved here. Over `k^sep`, `M` is a Levi subgroup containing a
maximal torus `T`, and `T` can be chosen with a base `Δ` of the roots of
`G` that contains a base `Δ_M` of the roots of `M`. The cocharacter
lattice `X_*(T ∩ M_der)` is the saturation of `ℤΔ_M^∨` in `X_*(T)`. For
simply connected `G` the simple coroots `Δ^∨` form a basis of `X_*(T)`,
so this saturation equals `ℤΔ_M^∨`. Hence the coroots of `M_der` span its
cocharacter lattice, and `M_der` is simply connected.

The same fact for Levi subgroups of parabolic subgroups is Remark 5.4.7 of
Brian Conrad, *Reductive group schemes* (Panoramas et Synthèses 42–43,
2014; registered as `conrad-2014-reductive-group-schemes`, PDF p. 178).
There `G` is semisimple and simply connected over a general base `S`. The
remark works étale-locally to reduce to `L = Z_G(λ)` for a closed subtorus
`λ : G_m ↪ T` of a maximal torus `T ⊂ G`, and refers to
Exercise 6.5.2(iv). Applying that remark to the centralizer `M` here still
requires the comparison between centralizers of split subtori and Levi
subgroups of parabolic subgroups, which is part of proving this
proposition.

Splitness of `A` is not used by the argument above. It is kept so that
this proposition has the same hypotheses as the companion statement
`SplitTorusCentralizerCocenterInducedStatement`.

This module supplies no proof. The proof is a separate obligation.
