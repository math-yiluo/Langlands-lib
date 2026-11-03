# Quotients of affine algebraic groups by normal closed subgroups: statement

Worker 1400 and Worker 1406.

This module defines one proposition and proves nothing. It constructs no
quotient. A proof of the proposition is a separate task.

## `NormalSubgroupQuotientExistenceStatement`

`NormalSubgroupQuotientExistenceStatement.{u}` says: for every field
`k : Type u`, all group schemes `G` and `N` over `Spec k` and every
group-scheme homomorphism `i : N ⟶ G` such that

1. the structure morphism `G.X.hom` is affine (`IsAffineHom`) and locally of
   finite type, so `G` is an affine group scheme of finite type over `k`;
2. `IsClosedSubgroup i`: the underlying scheme morphism of `i` is a closed
   immersion;
3. `(SubgroupFunctor.range i).IsNormal`: on every test scheme `T` over
   `Spec k`, the image of `N(T)` in `G(T)` is a normal subgroup of `G(T)`
   (`SubgroupFunctor.IsNormal F` is `F.IsNormalizedBy ⊤`),

there are a group scheme `Q` over `Spec k` and a group-scheme homomorphism
`q : G ⟶ Q` such that

1. `Q.X.hom` is affine and locally of finite type;
2. `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`, the published
   predicate of `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`,
   used unchanged. It says: the underlying scheme morphism of `q` is flat,
   surjective and locally of finite presentation, and the range functor of
   the actual pullback kernel `kernelι q` (published in
   `Langlands.AbelianScheme.Kernel`) equals the range functor of `i` on every
   test scheme over `Spec k`.

The field is arbitrary and the universe `u` is arbitrary; `Q` lives over the
same base `Spec k` and in the same universe as `G`. Neither `G` nor `N` is
assumed smooth, reduced or connected, so infinitesimal normal subgroups such as
`μ_p` in characteristic `p` are covered. Surjectivity is surjectivity of the
map of underlying topological spaces, not of rational points or of points on
each test scheme. The statement asserts only existence; it does not state a
universal property of `q`, and it does not assert that `Q` is unique.

The kernel condition compares subgroup functors on all test schemes over
`Spec k`, not only on affine ones, and not only on rational points. Since `i`
is a closed immersion, `SubgroupFunctor.range i` is the functor of points of
the closed subscheme `N` of `G`.

## Sources

- J. S. Milne, *Algebraic Groups* (2017), source ID
  `milne-2017-algebraic-groups`.
  - Proposition 5.18, printed p.103 / PDF p.119: every normal algebraic
    subgroup `N` of an affine algebraic group `G` is the kernel of a quotient
    map `G → Q` with `Q` affine. Theorem 5.14, printed p.102 / PDF p.118,
    is the same statement without affineness; the text after the proof of
    5.18 records that 5.18 proves 5.14 for affine `G`.
  - Definition 5.5, printed p.99 / PDF p.115: a homomorphism of algebraic
    groups is a quotient map if it is faithfully flat, i.e. flat and
    surjective.
  - Definition 1.1, printed p.6 / PDF p.22: an algebraic group is a group
    object in algebraic schemes over `k`, i.e. schemes of finite type over
    `k`. Definition 1.3, printed p.7 / PDF p.23: an algebraic subgroup is an
    algebraic group that is a `k`-subscheme with homomorphic inclusion.
    Proposition 1.41, printed p.18 / PDF p.34: algebraic subgroups of
    algebraic groups are closed (in the Zariski topology).
    Definition 1.51(a), printed p.21 / PDF p.37: an algebraic subgroup `H` is
    normal if `H(R)` is normal in `G(R)` for all `k`-algebras `R`.

The official Milne errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no correction to the
statements of 1.1, 1.3, 1.41, 1.51, 5.5, 5.14 or 5.18; its only Chapter 5
correction concerns Exercise 5-7. It does flag the proof of Lemma 1.40
(p.18), which the proof of 1.41 uses, as incomplete and says that a correct
proof is not difficult; the statement of 1.41 is unchanged.

## Derived packaging

Milne states the result for algebraic groups and `k`-algebras. The Lean
statement transcribes it as follows; these are formalization choices, not
claims of the source.

- "Affine algebraic group" is encoded as an affine, locally finite type
  structure morphism. Over a field these together give finite type.
- "Algebraic subgroup" is encoded as a group-scheme homomorphism `i` whose
  scheme morphism is a closed immersion. Milne's algebraic subgroups are
  `k`-subschemes, and by his Proposition 1.41 they are closed, so the
  statement covers them; `N` is given as an abstract group scheme with a
  homomorphic closed immersion rather than as a subscheme of `G`.
- Normality is required on every test scheme over `Spec k` through the
  Library's `SubgroupFunctor.IsNormal`, rather than on `k`-algebras only.
- "Quotient map" becomes flat and surjective. Local finite presentation is
  not named in the source; it holds for any morphism of schemes of finite
  type over a field, and is recorded so that `q` is an fppf morphism, as in
  `RelativeRoot.IsFppfQuotient`.
- "Kernel `N`" becomes equality of subgroup functors on all test schemes
  between the range of the actual kernel `kernelι q` and the range of `i`.
- The affineness of `Q` and the finite type of `Q` (Milne's `Q` is an
  algebraic group) are recorded as conclusions.

This module does not prove that these encodings agree with Milne's notions;
the statement takes them as its definitions.

## Related Library statements

- `NormalSubgroupQuotientStatement` (module
  `Langlands.GroupScheme.NormalSubgroupQuotientStatement`) has the same
  hypotheses on `i` and the same `IsFppfQuotient` conclusion, but assumes `G`
  smooth and concludes that `Q` is smooth. Neither statement assumes `N`
  smooth, so a nonsmooth normal subgroup of a smooth affine `G`, such as a
  possibly nonsmooth centre, is already covered by the existing statement.
  The present statement extends it to nonsmooth ambient groups `G` and
  asserts nothing about smoothness of `Q`.
- `SmoothSubgroupQuotientExistenceStatement` (module
  `Langlands.GroupScheme.HomogeneousQuotientStatement`) treats smooth
  subgroups without normality.
