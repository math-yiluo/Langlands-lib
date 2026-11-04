# Reflection of algebraic simple connectedness along algebraic field extensions

Author: Worker 1429.

This module defines the proposition
`Langlands.GroupScheme.SimplyConnectedAlgebraicExtensionReflectionStatement.{u}`.
It states that simple connectedness descends from an algebraic scalar
extension to the original field group. It proves nothing. Its only import is the
unchanged module `Langlands.GroupScheme.SimplyConnected.Basic`, which supplies
`IsSimplyConnected` and, through its imports, `IsSemisimple`,
`IsCentralIsogeny` and `GroupScheme.baseChange`.

## Quantifiers and actual base change

The universe `u` is arbitrary. The proposition quantifies over every pair
`k K : Type u` and every field structure on each. It also quantifies over every
`Algebra k K` with `Algebra.IsAlgebraic k K`: every element of `K` is a root
of a nonzero polynomial with coefficients in `k`. The extension may be finite
or infinite. It may be separable, inseparable or purely inseparable. It need
not be normal. Neither field need be perfect, and there is no characteristic
restriction, so algebraic extensions of imperfect fields of positive
characteristic are included. Transcendental extensions are excluded by the
`Algebra.IsAlgebraic` hypothesis. Finally, the proposition quantifies over every actual
`G : GroupScheme (Spec (CommRingCat.of k))`, a group object in the category of
schemes over `Spec k`.

Write

```text
b   = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k,
G_K = (GroupScheme.baseChange b).obj G.
```

These names abbreviate the terms written inline in Lean. `b` is the same map
as the existing `Langlands.GroupScheme.algebraBaseMap k K`. The unchanged
functor `GroupScheme.baseChange b` is `(Over.pullback b).mapGrp`, so `G_K` is
the fibre product `G ×_{Spec k} Spec K` over `Spec K` with the pulled-back
group law. No other model of scalar extension is used.

The proposition is exactly

```text
IsSimplyConnected G_K → IsSimplyConnected G.
```

Its only hypothesis on `G` is simple connectedness of `G_K`. Semisimplicity,
reductivity, smoothness, affineness, connectedness, finite type and a finite
centre are not assumed for `G`. They are part of the conclusion through its
semisimplicity field. The proposition contains no covering datum or chosen
cover. It also takes none of the following as a premise: semisimplicity
ascent or reflection, base change of central isogenies, or fpqc descent.

## The unchanged predicates

All predicates are the published ones, unchanged.

`IsSimplyConnected G` is a structure with two fields:

- `isSemisimple : IsSemisimple G`;
- `central_isogeny_isIso`: for every `H : GroupScheme (Spec (CommRingCat.of k))`
  and every homomorphism `f : H ⟶ G`, if `IsSemisimple H` and
  `IsCentralIsogeny f`, then `IsIso f`.

Here `IsIso f` is invertibility in the category of group schemes over
`Spec k`. Over `K` the incoming groups `H` range over all semisimple
`K`-groups, not only scalar extensions of `k`-groups. Over `k` the conclusion
requires the second field for every semisimple `k`-group `H` and every
incoming central isogeny into `G`.

`IsSemisimple G` has two fields:

- `IsConnectedReductive G`: the structural morphism is smooth and affine, the
  underlying space is connected, and the unipotent radical is trivial after
  base change to an algebraic closure of the field.
- `HasFiniteCenter G`: there are an actual group scheme `Z` over the same base
  and an actual homomorphism `z : Z ⟶ G` with `IsSchemeTheoreticCenter z` and
  `IsFinite Z.X.hom`. Here `IsSchemeTheoreticCenter z` means that the
  underlying morphism is a closed immersion and
  `SubgroupFunctor.range z = center G`.

The centre functor `center G` is tested on every scheme `T` over the base,
including nonreduced ones. A point `g` on `T` is central when, for every
`T' ⟶ T`, its restriction commutes with every point of `G` on `T'`. The
representative `Z` keeps its nilpotents and need not be smooth, reduced or
connected. Finiteness is finiteness of its structural morphism.

For the incoming homomorphism `f : H ⟶ G` above, `IsCentralIsogeny f` has
three fields:

- `IsIsogeny f`: the underlying scheme morphism is finite, flat and
  surjective;
- the underlying scheme morphism is locally of finite presentation;
- `IsCentral (kernelι f)`: the actual kernel is central in the source `H`.

The kernel is the full scheme-theoretic one: `kernel f` is the pullback of `f`
along the unit section of the target `G`, and `kernelι f : kernel f ⟶ H` is its
inclusion into the source `H`. By definition, `IsCentral (kernelι f)` says
that for every scheme `T` over the base, every point of `kernel f` on `T`,
composed with `kernelι f`, lies in `center H` on `T`. By the published
`isCentral_iff_range_le_center` and `isCentral_kernelι_iff` in
`Langlands.GroupScheme.CentralIsogeny.Basic`, this is equivalent to
`SubgroupFunctor.range (kernelι f) ≤ center H`, and to: every point `x` of `H`
on `T` with `x ≫ f = 1` lies in `center H` on `T`. By the definition of
`center H`, the latter means that for every `T' ⟶ T` the restriction of `x`
commutes with every point of `H` on `T'`. Nonreduced test
schemes are included. Non-smooth kernels, such as `μ_p` in characteristic `p`,
therefore count, and no reduced or smooth kernel is substituted.

## What is not asserted

This proposition states only the direction from `K` down to `k`, and only for
algebraic `K/k`. It asserts no reflection along transcendental extensions. It
asserts no ascent of simple connectedness: that is the separate
`IsSimplyConnectedFieldExtensionStatement` in
`Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement`. It asserts no
reflection of semisimplicity alone. For arbitrary extensions that is the separate
`SemisimpleFieldReflectionStatement` in
`Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionStatement`. It
asserts no universal-cover factorization and no existence of simply connected
covers; in particular, `SimplyConnectedCoverExistenceStatement` and every
module it imports are left unchanged. None of these propositions is implied by,
or assumed in, the present one.

## Sources and provenance

This is derived internal content. Its formulation was requested as a focused
prerequisite of the project's arbitrary-field simply connected cover-existence
work. It specializes a classical consequence of the literature to the Library's
exact predicates. It is restricted to algebraic extensions because the
project's proof route for semisimplicity ascent and reflection covers that case.

Mathematical sources:

- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second
  edition (2015), source `conrad-gabber-prasad-2015-pseudo-reductive`. The
  paragraph just before Corollary A.4.11, printed p.500 (PDF p.526), defines a
  connected semisimple group to be simply connected when every central isogeny
  `G' → G` from a connected semisimple group is an isomorphism. Corollary
  A.4.11(1), printed pp.500-501 (PDF pp.526-527), gives a simply connected
  central cover `π : G̃ → G`, unique up to unique isomorphism, whose "formation
  commutes with any extension of the base field". Hence, classically, if
  `G_K` is simply connected then `π_K` is an isomorphism, and descent makes `π`
  an isomorphism. That argument presupposes that `G` is semisimple. The Lean
  statement does not presuppose this; it concludes it. The registered author
  page check `conrad-author-books-errata-check-2026-11-02` shows no dedicated
  errata link for this book; this is not a claim that no corrections exist.
- J. S. Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`.
  Proposition 19.15, printed p.400 (PDF p.416), states the central-isogeny
  criterion that `IsSimplyConnected` uses. The remark after its proof, printed
  p.401 (PDF p.417), calls this criterion the usual definition and cites CGP
  p.500. Definition
  18.5, printed p.388 (PDF p.404), is Milne's multiplicative-isogeny
  definition. Proposition 19.13, printed p.400, gives reductivity of `G` if
  and only if `G_{k'}` is reductive for an extension field `k'`. Proposition
  19.10 on the same page characterizes semisimple reductive groups by
  finiteness of the centre, which may be nonsmooth and disconnected. These
  pages were read. The retained official errata snapshot
  `milne-2017-algebraic-groups-errata-2026-11-02` corrects 18.4, 18.8, 19.7 and
  19.8, and does not correct 18.5, 19.10, 19.13 or 19.15.

Milne and CGP work with algebraic groups of finite type over a field. The
Lean proposition quantifies over every actual group scheme over `Spec k` and
uses the Library's finite-centre form of semisimplicity. A proof must therefore
establish every needed descent and predicate comparison at that generality.

Intended internal proof route. It is recorded only to explain why this target
is focused; none of its steps is a premise of the proposition.

1. Reflect `IsSemisimple G_K` to `IsSemisimple G` along the algebraic
   extension.
2. For a semisimple `k`-group `H` and a central isogeny `f : H ⟶ G`, ascend
   semisimplicity to `H_K` along the algebraic extension.
3. The published `IsCentralIsogeny.baseChange` in
   `Langlands.GroupScheme.CentralIsogeny.BaseChange` makes the actual
   extended map `(GroupScheme.baseChange b).map f` a central isogeny.
   Simple connectedness of `G_K` makes it an isomorphism.
4. The published `fieldExtension_fpqc` and `isIso_of_baseChange` in
   `Langlands.GroupScheme.BaseChangeReflection` reflect that isomorphism to
   `IsIso f`.

This is the argument of the published conditional
`IsSimplyConnected.of_fieldExtension` in
`Langlands.GroupScheme.SimplyConnected.GeometricReduction`. That theorem
assumes semisimplicity ascent for arbitrary extensions, central-isogeny base
change and `IsSemisimple G`. Steps 1 and 2 replace its first and last
premises with algebraic-extension reflection and ascent of semisimplicity.
Those are separate proof obligations with their own statement reviews. They
are not part of this module.
